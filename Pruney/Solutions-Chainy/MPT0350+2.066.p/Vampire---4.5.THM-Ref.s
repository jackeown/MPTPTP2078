%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:59 EST 2020

% Result     : Theorem 13.27s
% Output     : Refutation 13.46s
% Verified   : 
% Statistics : Number of formulae       : 1260 (53701 expanded)
%              Number of leaves         :  182 (16297 expanded)
%              Depth                    :   21
%              Number of atoms          : 3265 (173635 expanded)
%              Number of equality atoms :  582 (50341 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16523,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f143,f156,f172,f177,f196,f212,f213,f228,f233,f276,f285,f317,f332,f390,f396,f402,f408,f414,f416,f422,f424,f430,f438,f496,f498,f565,f616,f665,f670,f710,f808,f830,f1058,f1065,f1071,f1384,f1745,f1750,f1751,f2180,f2210,f2224,f2229,f2403,f2404,f2408,f2409,f2779,f3911,f3916,f3921,f3923,f3931,f3935,f3940,f3942,f3951,f3957,f3963,f3987,f3995,f4013,f4020,f4034,f4050,f4096,f4103,f4107,f4111,f4127,f4248,f4249,f4355,f4356,f4424,f4425,f4426,f4531,f4642,f5054,f5061,f5068,f5076,f5079,f5086,f5090,f5093,f5101,f5107,f5108,f5114,f5115,f5121,f5122,f5128,f5129,f5130,f5131,f5132,f5133,f5134,f5135,f5136,f5137,f5139,f5141,f5143,f5149,f5150,f5156,f5157,f5164,f5165,f5166,f5167,f5168,f5169,f5170,f5171,f5172,f5173,f5175,f5177,f5179,f5186,f5187,f5194,f5195,f5196,f5197,f5198,f5199,f5200,f5201,f5202,f5203,f5205,f5207,f5210,f5212,f5214,f5216,f5218,f5220,f5222,f5224,f5227,f5228,f5229,f5251,f5267,f5268,f5270,f5275,f5320,f5391,f5398,f5402,f5405,f5412,f5417,f5419,f5420,f5619,f5642,f5643,f5645,f5650,f5652,f5653,f5655,f5656,f5662,f5663,f5665,f5670,f5672,f5673,f5675,f5676,f5682,f5683,f5685,f5690,f5692,f5693,f5695,f5696,f5704,f5712,f5716,f5724,f5732,f5737,f5739,f5740,f5743,f5748,f5750,f5752,f5756,f5757,f5759,f5761,f5769,f5775,f5778,f5780,f5784,f5785,f5787,f5789,f5792,f5793,f5795,f5796,f5801,f5804,f5805,f5807,f5809,f5812,f5814,f5816,f5824,f5832,f5840,f5843,f5847,f5848,f5859,f5864,f5866,f5869,f5876,f6023,f6098,f6103,f6108,f6151,f6174,f9422,f9949,f9954,f10534,f10646,f10651,f10652,f10660,f10670,f10679,f10689,f10692,f10695,f10702,f10707,f10708,f10713,f10718,f10719,f10965,f10980,f10993,f10996,f12101,f13121,f14010,f14016,f14063,f14066,f14081,f14082,f14089,f14100,f14124,f14793,f14968,f14997,f14999,f15001,f15003,f15006,f15009,f15011,f15014,f15016,f15021,f15022,f15024,f15026,f15028,f15031,f15034,f15036,f15039,f15041,f15046,f15052,f16378,f16383,f16522])).

fof(f16522,plain,
    ( ~ spl6_7
    | ~ spl6_47
    | spl6_150
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f16517,f4100,f419,f16519,f3928,f209])).

fof(f209,plain,
    ( spl6_7
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f3928,plain,
    ( spl6_47
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f16519,plain,
    ( spl6_150
  <=> sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).

fof(f419,plain,
    ( spl6_20
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f4100,plain,
    ( spl6_62
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f16517,plain,
    ( sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f16516,f6033])).

fof(f6033,plain,(
    ! [X38] : k4_xboole_0(X38,k1_xboole_0) = X38 ),
    inference(forward_demodulation,[],[f6032,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f6032,plain,(
    ! [X38] : k4_xboole_0(X38,k1_xboole_0) = k5_xboole_0(X38,k1_xboole_0) ),
    inference(forward_demodulation,[],[f5917,f499])).

fof(f499,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f477,f64])).

fof(f477,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f112,f198])).

fof(f198,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f62,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f112,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f5917,plain,(
    ! [X38] : k4_xboole_0(X38,k1_xboole_0) = k5_xboole_0(X38,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f238,f499])).

fof(f238,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f112,f113])).

fof(f113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f65,f69,f69])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f16516,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f16515,f7318])).

fof(f7318,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f7196,f7264])).

fof(f7264,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(forward_demodulation,[],[f7263,f7258])).

fof(f7258,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f7257,f499])).

fof(f7257,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f7230,f499])).

fof(f7230,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))) ),
    inference(unit_resulting_resolution,[],[f507,f507,f541,f299])).

fof(f299,plain,(
    ! [X14,X12,X13,X11] :
      ( r2_hidden(sK5(X11,X12,k5_xboole_0(X13,k4_xboole_0(X14,X13))),X14)
      | k4_xboole_0(X11,X12) = k5_xboole_0(X13,k4_xboole_0(X14,X13))
      | r2_hidden(sK5(X11,X12,k5_xboole_0(X13,k4_xboole_0(X14,X13))),X11)
      | r2_hidden(sK5(X11,X12,k5_xboole_0(X13,k4_xboole_0(X14,X13))),X13) ) ),
    inference(resolution,[],[f99,f150])).

fof(f150,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | r2_hidden(X4,X1)
      | r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f130,f114])).

fof(f114,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f111])).

fof(f111,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f110])).

fof(f110,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f87,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f102,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f103,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f104,f105])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f87,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f90,f111])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f541,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(unit_resulting_resolution,[],[f124,f203])).

fof(f203,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k4_xboole_0(X3,X4))
      | ~ r1_tarski(X3,X4) ) ),
    inference(global_subsumption,[],[f133,f202])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,X3)
      | ~ r2_hidden(X5,k4_xboole_0(X3,X4))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f132,f115])).

fof(f132,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f507,plain,(
    ! [X17] : ~ r2_hidden(X17,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f506])).

fof(f506,plain,(
    ! [X17] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | ~ r2_hidden(X17,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f483,f499])).

fof(f483,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | ~ r2_hidden(X17,k4_xboole_0(k1_xboole_0,X16)) ) ),
    inference(superposition,[],[f132,f198])).

fof(f7263,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f7227,f499])).

fof(f7227,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
    inference(unit_resulting_resolution,[],[f507,f541,f541,f299])).

fof(f7196,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(unit_resulting_resolution,[],[f541,f541,f99])).

fof(f16515,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f16360,f4102])).

fof(f4102,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f4100])).

fof(f16360,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl6_20 ),
    inference(superposition,[],[f421,f1241])).

fof(f1241,plain,(
    ! [X23,X21,X22] :
      ( k4_xboole_0(X21,k4_xboole_0(X22,X23)) = X21
      | ~ r1_tarski(X21,X23)
      | ~ r1_tarski(X21,X22) ) ),
    inference(forward_demodulation,[],[f1240,f199])).

fof(f199,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f124,f115])).

fof(f1240,plain,(
    ! [X23,X21,X22] :
      ( k4_xboole_0(X21,k4_xboole_0(X22,X23)) = k4_xboole_0(X21,k4_xboole_0(X21,X21))
      | ~ r1_tarski(X21,X23)
      | ~ r1_tarski(X21,X22) ) ),
    inference(forward_demodulation,[],[f1239,f1116])).

fof(f1116,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f124,f374])).

fof(f374,plain,(
    ! [X6,X8,X7] :
      ( k4_xboole_0(X6,k4_xboole_0(X8,X7)) = k5_xboole_0(k4_xboole_0(X6,X8),k4_xboole_0(X6,k4_xboole_0(X6,X8)))
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f369,f114])).

fof(f369,plain,(
    ! [X6,X8,X7] :
      ( k4_xboole_0(X6,k4_xboole_0(X8,X7)) = k3_tarski(k6_enumset1(k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),X6))
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f116,f115])).

fof(f116,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(definition_unfolding,[],[f88,f111,f69])).

fof(f88,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1239,plain,(
    ! [X23,X21,X22] :
      ( k4_xboole_0(X21,k4_xboole_0(X22,X23)) = k5_xboole_0(k4_xboole_0(X21,X21),k4_xboole_0(X21,k4_xboole_0(X21,X21)))
      | ~ r1_tarski(X21,X23)
      | ~ r1_tarski(X21,X22) ) ),
    inference(forward_demodulation,[],[f1139,f525])).

fof(f525,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k5_xboole_0(X4,X4) ),
    inference(superposition,[],[f112,f199])).

fof(f1139,plain,(
    ! [X23,X21,X22] :
      ( k4_xboole_0(X21,k4_xboole_0(X22,X23)) = k5_xboole_0(k5_xboole_0(X21,X21),k4_xboole_0(X21,k5_xboole_0(X21,X21)))
      | ~ r1_tarski(X21,X23)
      | ~ r1_tarski(X21,X22) ) ),
    inference(superposition,[],[f374,f235])).

fof(f235,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f112,f115])).

fof(f421,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f419])).

fof(f16383,plain,
    ( spl6_149
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f16157,f209,f16380])).

fof(f16380,plain,
    ( spl6_149
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_149])])).

fof(f16157,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f211,f124,f1241])).

fof(f211,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f16378,plain,
    ( spl6_148
    | ~ spl6_28
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f16373,f1747,f707,f16375])).

fof(f16375,plain,
    ( spl6_148
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f707,plain,
    ( spl6_28
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1747,plain,
    ( spl6_36
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f16373,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl6_28
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f16158,f709])).

fof(f709,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f707])).

fof(f16158,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f1749,f124,f1241])).

fof(f1749,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f1747])).

fof(f15052,plain,
    ( ~ spl6_147
    | spl6_50
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f15047,f5058,f3944,f15049])).

fof(f15049,plain,
    ( spl6_147
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).

fof(f3944,plain,
    ( spl6_50
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f5058,plain,
    ( spl6_71
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f15047,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl6_50
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f3946,f5060])).

fof(f5060,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f5058])).

fof(f3946,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | spl6_50 ),
    inference(avatar_component_clause,[],[f3944])).

fof(f15046,plain,
    ( spl6_146
    | spl6_139 ),
    inference(avatar_split_clause,[],[f14971,f14097,f15043])).

fof(f15043,plain,
    ( spl6_146
  <=> r2_hidden(sK2(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_146])])).

fof(f14097,plain,
    ( spl6_139
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f14971,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f14098,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f14098,plain,
    ( k1_xboole_0 != sK1
    | spl6_139 ),
    inference(avatar_component_clause,[],[f14097])).

fof(f15041,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15040,f14097,f5058,f209,f14994])).

fof(f14994,plain,
    ( spl6_144
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f15040,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14973,f5060])).

fof(f14973,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f542,f542,f542,f542,f14098,f351])).

fof(f351,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X3)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | r2_hidden(sK4(X0,X1,X3),X0)
      | X2 = X3
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(superposition,[],[f147,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f120,f114])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f93,f111])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f542,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f211,f203])).

fof(f15039,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15038,f14097,f5058,f209,f14994])).

fof(f15038,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f15037,f7318])).

fof(f15037,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14974,f5060])).

fof(f14974,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(sK1,sK0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f541,f541,f542,f542,f14098,f351])).

fof(f15036,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15035,f14097,f5058,f209,f14994])).

fof(f15035,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14975,f5060])).

fof(f14975,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f542,f542,f14098,f351])).

fof(f15034,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15033,f14097,f5058,f209,f14994])).

fof(f15033,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f15032,f5060])).

fof(f15032,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(forward_demodulation,[],[f14976,f7318])).

fof(f14976,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,X0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f542,f542,f541,f541,f14098,f351])).

fof(f15031,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15030,f14097,f14994])).

fof(f15030,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f15029,f7318])).

fof(f15029,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f14977,f7318])).

fof(f14977,plain,
    ( ! [X0,X1] : r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1),sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f541,f541,f541,f541,f14098,f351])).

fof(f15028,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15027,f14097,f14994])).

fof(f15027,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f14978,f7318])).

fof(f14978,plain,
    ( ! [X0] : r2_hidden(sK4(k1_xboole_0,k4_xboole_0(X0,X0),sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f541,f541,f14098,f351])).

fof(f15026,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15025,f14097,f5058,f209,f14994])).

fof(f15025,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14979,f5060])).

fof(f14979,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f507,f14098,f351])).

fof(f15024,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15023,f14097,f14994])).

fof(f15023,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f14980,f7318])).

fof(f14980,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f541,f541,f507,f14098,f351])).

fof(f15022,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f14981,f14097,f14994])).

fof(f14981,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f507,f507,f14098,f351])).

fof(f15021,plain,
    ( spl6_145
    | spl6_139 ),
    inference(avatar_split_clause,[],[f14982,f14097,f15018])).

fof(f15018,plain,
    ( spl6_145
  <=> r2_hidden(sK2(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).

fof(f14982,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f14098,f78])).

fof(f15016,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15015,f14097,f5058,f209,f14994])).

fof(f15015,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14984,f5060])).

fof(f14984,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f542,f542,f14098,f351])).

fof(f15014,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15013,f14097,f5058,f209,f14994])).

fof(f15013,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f15012,f7318])).

fof(f15012,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14985,f5060])).

fof(f14985,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(sK1,sK0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f541,f541,f507,f542,f542,f14098,f351])).

fof(f15011,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15010,f14097,f5058,f209,f14994])).

fof(f15010,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14986,f5060])).

fof(f14986,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f542,f542,f14098,f351])).

fof(f15009,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15008,f14097,f5058,f209,f14994])).

fof(f15008,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f15007,f5060])).

fof(f15007,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(forward_demodulation,[],[f14987,f7318])).

fof(f14987,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,X0),sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f541,f541,f14098,f351])).

fof(f15006,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15005,f14097,f14994])).

fof(f15005,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f15004,f7318])).

fof(f15004,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f14988,f7318])).

fof(f14988,plain,
    ( ! [X0,X1] : r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1),sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f541,f541,f507,f541,f541,f14098,f351])).

fof(f15003,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15002,f14097,f14994])).

fof(f15002,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f14989,f7318])).

fof(f14989,plain,
    ( ! [X0] : r2_hidden(sK4(k1_xboole_0,k4_xboole_0(X0,X0),sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f541,f541,f14098,f351])).

fof(f15001,plain,
    ( spl6_144
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(avatar_split_clause,[],[f15000,f14097,f5058,f209,f14994])).

fof(f15000,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | ~ spl6_71
    | spl6_139 ),
    inference(forward_demodulation,[],[f14990,f5060])).

fof(f14990,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1)
    | ~ spl6_7
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f507,f14098,f351])).

fof(f14999,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f14998,f14097,f14994])).

fof(f14998,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(forward_demodulation,[],[f14991,f7318])).

fof(f14991,plain,
    ( ! [X0] : r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f541,f541,f507,f14098,f351])).

fof(f14997,plain,
    ( spl6_144
    | spl6_139 ),
    inference(avatar_split_clause,[],[f14992,f14097,f14994])).

fof(f14992,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)
    | spl6_139 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f507,f507,f14098,f351])).

fof(f14968,plain,
    ( spl6_142
    | ~ spl6_143 ),
    inference(avatar_split_clause,[],[f14947,f14965,f14962])).

fof(f14962,plain,
    ( spl6_142
  <=> ! [X40] :
        ( m1_subset_1(X40,k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(X40,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f14965,plain,
    ( spl6_143
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_143])])).

fof(f14947,plain,(
    ! [X40] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(X40,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X40,k1_xboole_0) ) ),
    inference(superposition,[],[f704,f499])).

fof(f704,plain,(
    ! [X59,X60] :
      ( ~ m1_subset_1(k4_xboole_0(X59,X60),k1_zfmisc_1(X59))
      | m1_subset_1(X60,k1_zfmisc_1(X59))
      | ~ r1_tarski(X60,X59) ) ),
    inference(superposition,[],[f223,f236])).

fof(f236,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f113,f115])).

fof(f223,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f14793,plain,
    ( spl6_140
    | ~ spl6_141 ),
    inference(avatar_split_clause,[],[f14785,f14790,f14787])).

fof(f14787,plain,
    ( spl6_140
  <=> ! [X29,X28,X30] :
        ( ~ r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29))))
        | ~ r1_tarski(X28,X29) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f14790,plain,
    ( spl6_141
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f14785,plain,(
    ! [X30,X28,X29] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29))))
      | ~ r1_tarski(X28,X29) ) ),
    inference(global_subsumption,[],[f507,f14784])).

fof(f14784,plain,(
    ! [X30,X28,X29] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | r2_hidden(X30,k1_xboole_0)
      | ~ r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29))))
      | ~ r1_tarski(X28,X29) ) ),
    inference(forward_demodulation,[],[f14783,f7318])).

fof(f14783,plain,(
    ! [X30,X28,X29] :
      ( r2_hidden(X30,k1_xboole_0)
      | ~ r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29))))
      | ~ r1_tarski(k4_xboole_0(X28,X28),k4_xboole_0(X28,X28))
      | ~ r1_tarski(X28,X29) ) ),
    inference(forward_demodulation,[],[f14584,f7318])).

fof(f14584,plain,(
    ! [X30,X28,X29] :
      ( ~ r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29))))
      | r2_hidden(X30,k4_xboole_0(X28,X28))
      | ~ r1_tarski(k4_xboole_0(X28,X28),k4_xboole_0(X28,X28))
      | ~ r1_tarski(X28,X29) ) ),
    inference(superposition,[],[f643,f373])).

fof(f373,plain,(
    ! [X6,X8,X7] :
      ( k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7))) = k5_xboole_0(k4_xboole_0(X6,X8),k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X8)))
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f366,f114])).

fof(f366,plain,(
    ! [X6,X8,X7] :
      ( k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7))) = k3_tarski(k6_enumset1(k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X6)))
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f116,f115])).

fof(f643,plain,(
    ! [X43,X41,X42] :
      ( ~ r2_hidden(X43,k5_xboole_0(X42,k4_xboole_0(X41,X41)))
      | r2_hidden(X43,X42)
      | ~ r1_tarski(X41,X42) ) ),
    inference(global_subsumption,[],[f543,f642])).

fof(f642,plain,(
    ! [X43,X41,X42] :
      ( ~ r2_hidden(X43,k5_xboole_0(X42,k4_xboole_0(X41,X41)))
      | r2_hidden(X43,X41)
      | r2_hidden(X43,X42)
      | ~ r1_tarski(X41,X42) ) ),
    inference(forward_demodulation,[],[f600,f525])).

fof(f600,plain,(
    ! [X43,X41,X42] :
      ( ~ r2_hidden(X43,k5_xboole_0(X42,k5_xboole_0(X41,X41)))
      | r2_hidden(X43,X41)
      | r2_hidden(X43,X42)
      | ~ r1_tarski(X41,X42) ) ),
    inference(superposition,[],[f150,f235])).

fof(f543,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f203,f131])).

fof(f131,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14124,plain,
    ( ~ spl6_115
    | spl6_126 ),
    inference(avatar_split_clause,[],[f11805,f10715,f9419])).

fof(f9419,plain,
    ( spl6_115
  <=> r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f10715,plain,
    ( spl6_126
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f11805,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_126 ),
    inference(unit_resulting_resolution,[],[f10717,f127])).

fof(f127,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f10717,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl6_126 ),
    inference(avatar_component_clause,[],[f10715])).

fof(f14100,plain,
    ( spl6_139
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f14095,f3908,f14097])).

fof(f3908,plain,
    ( spl6_44
  <=> sK1 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f14095,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f3910,f7318])).

fof(f3910,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f3908])).

fof(f14089,plain,
    ( spl6_138
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f14084,f4528,f14086])).

fof(f14086,plain,
    ( spl6_138
  <=> sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).

fof(f4528,plain,
    ( spl6_68
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f14084,plain,
    ( sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f14083,f6033])).

fof(f14083,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f4530,f7318])).

fof(f4530,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f4528])).

fof(f14082,plain,
    ( ~ spl6_115
    | spl6_125 ),
    inference(avatar_split_clause,[],[f13183,f10710,f9419])).

fof(f10710,plain,
    ( spl6_125
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f13183,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_125 ),
    inference(unit_resulting_resolution,[],[f61,f10712,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f10712,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_125 ),
    inference(avatar_component_clause,[],[f10710])).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f14081,plain,
    ( spl6_137
    | ~ spl6_115
    | spl6_125 ),
    inference(avatar_split_clause,[],[f13184,f10710,f9419,f14078])).

fof(f14078,plain,
    ( spl6_137
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f13184,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | spl6_125 ),
    inference(resolution,[],[f10712,f72])).

fof(f14066,plain,
    ( ~ spl6_7
    | spl6_136
    | spl6_43 ),
    inference(avatar_split_clause,[],[f13887,f3904,f14014,f209])).

fof(f14014,plain,
    ( spl6_136
  <=> ! [X594] :
        ( ~ r1_tarski(sK1,k4_xboole_0(sK1,X594))
        | ~ r1_tarski(sK1,X594) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f3904,plain,
    ( spl6_43
  <=> r1_tarski(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f13887,plain,
    ( ! [X594] :
        ( ~ r1_tarski(sK1,k4_xboole_0(sK1,X594))
        | ~ r1_tarski(sK1,sK0)
        | ~ r1_tarski(sK1,X594) )
    | spl6_43 ),
    inference(superposition,[],[f3906,f584])).

fof(f584,plain,(
    ! [X2,X3,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X1,X3)
      | ~ r1_tarski(X1,X3)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f235,f235])).

fof(f3906,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f3904])).

fof(f14063,plain,
    ( ~ spl6_134
    | spl6_135
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f13860,f411,f14008,f14004])).

fof(f14004,plain,
    ( spl6_134
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).

fof(f14008,plain,
    ( spl6_135
  <=> ! [X556] :
        ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),X556))
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),X556) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f411,plain,
    ( spl6_19
  <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f13860,plain,
    ( ! [X556] :
        ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),X556))
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),X556) )
    | ~ spl6_19 ),
    inference(superposition,[],[f413,f584])).

fof(f413,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f411])).

fof(f14016,plain,
    ( ~ spl6_7
    | spl6_136
    | spl6_43 ),
    inference(avatar_split_clause,[],[f13703,f3904,f14014,f209])).

fof(f13703,plain,
    ( ! [X594] :
        ( ~ r1_tarski(sK1,k4_xboole_0(sK1,X594))
        | ~ r1_tarski(sK1,X594)
        | ~ r1_tarski(sK1,sK0) )
    | spl6_43 ),
    inference(superposition,[],[f3906,f584])).

fof(f14010,plain,
    ( ~ spl6_134
    | spl6_135
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f13676,f411,f14008,f14004])).

fof(f13676,plain,
    ( ! [X556] :
        ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),X556))
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),X556)
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1) )
    | ~ spl6_19 ),
    inference(superposition,[],[f413,f584])).

fof(f13121,plain,
    ( spl6_132
    | spl6_133
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f13113,f169,f13118,f13115])).

fof(f13115,plain,
    ( spl6_132
  <=> ! [X264] : ~ r1_tarski(k1_zfmisc_1(sK0),X264) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f13118,plain,
    ( spl6_133
  <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f169,plain,
    ( spl6_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f13113,plain,
    ( ! [X264] :
        ( r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(sK0)))
        | ~ r1_tarski(k1_zfmisc_1(sK0),X264) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f12865,f7264])).

fof(f12865,plain,
    ( ! [X264] :
        ( r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),X264),k1_zfmisc_1(sK0)))
        | ~ r1_tarski(k1_zfmisc_1(sK0),X264) )
    | ~ spl6_4 ),
    inference(superposition,[],[f215,f1235])).

fof(f1235,plain,(
    ! [X12,X13] :
      ( k4_xboole_0(X12,k4_xboole_0(k4_xboole_0(X12,X12),X13)) = X12
      | ~ r1_tarski(X12,X13) ) ),
    inference(forward_demodulation,[],[f1136,f526])).

fof(f526,plain,(
    ! [X6] : k5_xboole_0(X6,k4_xboole_0(X6,X6)) = X6 ),
    inference(superposition,[],[f112,f199])).

fof(f1136,plain,(
    ! [X12,X13] :
      ( k5_xboole_0(X12,k4_xboole_0(X12,X12)) = k4_xboole_0(X12,k4_xboole_0(k4_xboole_0(X12,X12),X13))
      | ~ r1_tarski(X12,X13) ) ),
    inference(superposition,[],[f374,f199])).

fof(f215,plain,
    ( ! [X0] : r2_hidden(sK1,k5_xboole_0(X0,k4_xboole_0(k1_zfmisc_1(sK0),X0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f148])).

fof(f148,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(forward_demodulation,[],[f128,f114])).

fof(f128,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f92,f111])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f171,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f169])).

fof(f12101,plain,
    ( spl6_131
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f12096,f1747,f12098])).

fof(f12098,plain,
    ( spl6_131
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f12096,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f11809,f7318])).

fof(f11809,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f1749,f1247])).

fof(f1247,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f1246,f112])).

fof(f1246,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f1153,f1116])).

fof(f1153,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f112,f374])).

fof(f10996,plain,
    ( ~ spl6_127
    | spl6_128
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f10953,f411,f10962,f10958])).

fof(f10958,plain,
    ( spl6_127
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f10962,plain,
    ( spl6_128
  <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f10953,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK1)
    | ~ spl6_19 ),
    inference(superposition,[],[f413,f687])).

fof(f687,plain,(
    ! [X8,X7] :
      ( k4_xboole_0(X7,X8) = k5_xboole_0(X7,X8)
      | ~ r1_tarski(X8,X7) ) ),
    inference(superposition,[],[f112,f236])).

fof(f10993,plain,
    ( ~ spl6_129
    | spl6_130
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f10992,f4100,f419,f10977,f10973])).

fof(f10973,plain,
    ( spl6_129
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f10977,plain,
    ( spl6_130
  <=> sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f10992,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f10991,f6033])).

fof(f10991,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f10990,f7318])).

fof(f10990,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f10947,f4102])).

fof(f10947,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20 ),
    inference(superposition,[],[f421,f687])).

fof(f10980,plain,
    ( ~ spl6_129
    | spl6_130
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f10971,f4100,f419,f10977,f10973])).

fof(f10971,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f10970,f6033])).

fof(f10970,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f10969,f7318])).

fof(f10969,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f10905,f4102])).

fof(f10905,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_20 ),
    inference(superposition,[],[f687,f421])).

fof(f10965,plain,
    ( ~ spl6_127
    | spl6_128
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f10897,f411,f10962,f10958])).

fof(f10897,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK1)
    | ~ spl6_19 ),
    inference(superposition,[],[f687,f413])).

fof(f10719,plain,
    ( ~ spl6_126
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10640,f9419,f10715])).

fof(f10640,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl6_115 ),
    inference(resolution,[],[f9421,f126])).

fof(f126,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9421,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_115 ),
    inference(avatar_component_clause,[],[f9419])).

fof(f10718,plain,
    ( ~ spl6_126
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10593,f9419,f10715])).

fof(f10593,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f9421,f126])).

fof(f10713,plain,
    ( ~ spl6_125
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10594,f9419,f10710])).

fof(f10594,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f61,f9421,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10708,plain,
    ( spl6_123
    | ~ spl6_4
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10595,f9419,f169,f10699])).

fof(f10699,plain,
    ( spl6_123
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f10595,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_4
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f171,f9421,f131])).

fof(f10707,plain,
    ( spl6_124
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10596,f9419,f10704])).

fof(f10704,plain,
    ( spl6_124
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f10596,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f161,f9421,f131])).

fof(f161,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f124,f126])).

fof(f10702,plain,
    ( spl6_123
    | ~ spl6_29
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10697,f9419,f805,f10699])).

fof(f805,plain,
    ( spl6_29
  <=> r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f10697,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_29
    | spl6_115 ),
    inference(forward_demodulation,[],[f10600,f1231])).

fof(f1231,plain,(
    ! [X8] : k5_xboole_0(k4_xboole_0(X8,X8),X8) = X8 ),
    inference(global_subsumption,[],[f124,f1130])).

fof(f1130,plain,(
    ! [X8] :
      ( k5_xboole_0(k4_xboole_0(X8,X8),X8) = X8
      | ~ r1_tarski(X8,X8) ) ),
    inference(superposition,[],[f374,f199])).

fof(f10600,plain,
    ( r2_hidden(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_29
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f807,f9421,f131])).

fof(f807,plain,
    ( r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f805])).

fof(f10695,plain,
    ( ~ spl6_120
    | ~ spl6_7
    | ~ spl6_71
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10694,f9419,f5058,f209,f10657])).

fof(f10657,plain,
    ( spl6_120
  <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f10694,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_7
    | ~ spl6_71
    | spl6_115 ),
    inference(forward_demodulation,[],[f10693,f6033])).

fof(f10693,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl6_7
    | ~ spl6_71
    | spl6_115 ),
    inference(forward_demodulation,[],[f10607,f5060])).

fof(f10607,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(sK1,sK0))))
    | ~ spl6_7
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f542,f9421,f150])).

fof(f10692,plain,
    ( ~ spl6_120
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10691,f9419,f10657])).

fof(f10691,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10690,f6033])).

fof(f10690,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10608,f7318])).

fof(f10608,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(X0,X0))))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f541,f9421,f150])).

fof(f10689,plain,
    ( ~ spl6_120
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10688,f9419,f10657])).

fof(f10688,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10610,f6033])).

fof(f10610,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f507,f9421,f150])).

fof(f10679,plain,
    ( ~ spl6_122
    | ~ spl6_4
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10674,f9419,f169,f10676])).

fof(f10676,plain,
    ( spl6_122
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f10674,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_4
    | spl6_115 ),
    inference(forward_demodulation,[],[f10673,f1116])).

fof(f10673,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)))))
    | ~ spl6_4
    | spl6_115 ),
    inference(forward_demodulation,[],[f10622,f113])).

fof(f10622,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl6_4
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f205,f9421,f289])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))
      | r2_hidden(X2,X0)
      | r2_hidden(X2,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f150,f113])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f132])).

fof(f10670,plain,
    ( ~ spl6_121
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10665,f9419,f10667])).

fof(f10667,plain,
    ( spl6_121
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f10665,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10664,f1116])).

fof(f10664,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK1)),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK1)))))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10624,f113])).

fof(f10624,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK1)),k4_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)))))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f460,f9421,f289])).

fof(f460,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f161,f132])).

fof(f10660,plain,
    ( ~ spl6_120
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10655,f9419,f10657])).

fof(f10655,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10654,f6033])).

fof(f10654,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)))
    | spl6_115 ),
    inference(forward_demodulation,[],[f10628,f5434])).

fof(f5434,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f178,f461,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f117,f114])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f89,f111])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f461,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f61,f161,f72])).

fof(f178,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f61,f160,f72])).

fof(f160,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f62,f126])).

fof(f10628,plain,
    ( ~ r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0,k1_zfmisc_1(k1_xboole_0)))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f507,f178,f461,f9421,f310])).

fof(f310,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_subset_1(X2,X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f150,f144])).

fof(f10652,plain,
    ( ~ spl6_118
    | ~ spl6_4
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10630,f9419,f169,f10643])).

fof(f10643,plain,
    ( spl6_118
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f10630,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f171,f9421,f543])).

fof(f10651,plain,
    ( ~ spl6_119
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10631,f9419,f10648])).

fof(f10648,plain,
    ( spl6_119
  <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f10631,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f161,f9421,f543])).

fof(f10646,plain,
    ( ~ spl6_118
    | ~ spl6_29
    | spl6_115 ),
    inference(avatar_split_clause,[],[f10641,f9419,f805,f10643])).

fof(f10641,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_29
    | spl6_115 ),
    inference(forward_demodulation,[],[f10635,f1231])).

fof(f10635,plain,
    ( ~ r1_tarski(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_29
    | spl6_115 ),
    inference(unit_resulting_resolution,[],[f807,f9421,f543])).

fof(f10534,plain,
    ( ~ spl6_117
    | spl6_14 ),
    inference(avatar_split_clause,[],[f10477,f329,f10531])).

fof(f10531,plain,
    ( spl6_117
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f329,plain,
    ( spl6_14
  <=> r2_hidden(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f10477,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f161,f331,f543])).

fof(f331,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f329])).

fof(f9954,plain,
    ( ~ spl6_116
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f9953,f169,f9946])).

fof(f9946,plain,
    ( spl6_116
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f9953,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_xboole_0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f9931,f7318])).

fof(f9931,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f551])).

fof(f551,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k4_xboole_0(X9,X9))
      | ~ r2_hidden(X10,X9) ) ),
    inference(superposition,[],[f203,f199])).

fof(f9949,plain,
    ( ~ spl6_116
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f9944,f805,f9946])).

fof(f9944,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_xboole_0)
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f9943,f1231])).

fof(f9943,plain,
    ( ~ r1_tarski(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0)
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f9935,f7318])).

fof(f9935,plain,
    ( ~ r1_tarski(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f551])).

fof(f9422,plain,
    ( ~ spl6_115
    | spl6_43
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f9417,f5058,f3904,f9419])).

fof(f9417,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl6_43
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f9416,f5060])).

fof(f9416,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK1,sK0)))
    | spl6_43 ),
    inference(unit_resulting_resolution,[],[f3906,f127])).

fof(f6174,plain,
    ( ~ spl6_114
    | spl6_67 ),
    inference(avatar_split_clause,[],[f6169,f4524,f6171])).

fof(f6171,plain,
    ( spl6_114
  <=> r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f4524,plain,
    ( spl6_67
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f6169,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | spl6_67 ),
    inference(unit_resulting_resolution,[],[f4526,f127])).

fof(f4526,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | spl6_67 ),
    inference(avatar_component_clause,[],[f4524])).

fof(f6151,plain,(
    spl6_113 ),
    inference(avatar_split_clause,[],[f6150,f6020])).

fof(f6020,plain,
    ( spl6_113
  <=> k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f6150,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6149,f499])).

fof(f6149,plain,(
    ! [X182,X183] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X183),X182)) ),
    inference(forward_demodulation,[],[f5989,f472])).

fof(f472,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f198,f113])).

fof(f5989,plain,(
    ! [X182,X183] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X183),X182)) = k3_tarski(k6_enumset1(k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k1_xboole_0)) ),
    inference(superposition,[],[f361,f499])).

fof(f361,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k3_tarski(k6_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[],[f116,f113])).

fof(f6108,plain,(
    spl6_113 ),
    inference(avatar_split_clause,[],[f6107,f6020])).

fof(f6107,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6106,f499])).

fof(f6106,plain,(
    ! [X132,X133] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X132,X133)) ),
    inference(forward_demodulation,[],[f5961,f472])).

fof(f5961,plain,(
    ! [X132,X133] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X132,X133)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(X133,k4_xboole_0(X133,k1_xboole_0)))) ),
    inference(superposition,[],[f367,f499])).

fof(f367,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X2,X1)) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f116,f113])).

fof(f6103,plain,(
    spl6_113 ),
    inference(avatar_split_clause,[],[f6102,f6020])).

fof(f6102,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6101,f499])).

fof(f6101,plain,(
    ! [X128,X129] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X128,k4_xboole_0(k1_xboole_0,X129))) ),
    inference(forward_demodulation,[],[f5959,f499])).

fof(f5959,plain,(
    ! [X128,X129] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X128,k4_xboole_0(k1_xboole_0,X129))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X129,k4_xboole_0(X129,k1_xboole_0))))) ),
    inference(superposition,[],[f364,f499])).

fof(f364,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[],[f116,f113])).

fof(f6098,plain,(
    spl6_113 ),
    inference(avatar_split_clause,[],[f6097,f6020])).

fof(f6097,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6096,f499])).

fof(f6096,plain,(
    ! [X125,X124] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X125),X124)) ),
    inference(forward_demodulation,[],[f6095,f472])).

fof(f6095,plain,(
    ! [X125,X124] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X125),X124)) = k3_tarski(k6_enumset1(k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f5957,f6033])).

fof(f5957,plain,(
    ! [X125,X124] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X125),X124)) = k3_tarski(k6_enumset1(k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f361,f499])).

fof(f6023,plain,(
    spl6_113 ),
    inference(avatar_split_clause,[],[f6018,f6020])).

fof(f6018,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6017,f499])).

fof(f6017,plain,(
    ! [X6,X7] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f5899,f499])).

fof(f5899,plain,(
    ! [X6,X7] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)))) ),
    inference(superposition,[],[f116,f499])).

fof(f5876,plain,
    ( spl6_112
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f5871,f5745,f5873])).

fof(f5873,plain,
    ( spl6_112
  <=> k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f5745,plain,
    ( spl6_104
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f5871,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_104 ),
    inference(forward_demodulation,[],[f5747,f5833])).

fof(f5833,plain,(
    ! [X0] : k4_subset_1(X0,X0,X0) = X0 ),
    inference(forward_demodulation,[],[f5435,f526])).

fof(f5435,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(unit_resulting_resolution,[],[f461,f461,f144])).

fof(f5747,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f5745])).

fof(f5869,plain,
    ( spl6_110
    | ~ spl6_2
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f5868,f5058,f140,f5856])).

fof(f5856,plain,
    ( spl6_110
  <=> sK0 = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f140,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f5868,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5867,f64])).

fof(f5867,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5424,f5060])).

fof(f5424,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f461,f144])).

fof(f142,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f5866,plain,
    ( spl6_111
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5865,f225,f193,f5861])).

fof(f5861,plain,
    ( spl6_111
  <=> k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f193,plain,
    ( spl6_6
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f225,plain,
    ( spl6_8
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f5865,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5425,f227])).

fof(f227,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f225])).

fof(f5425,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(k3_subset_1(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f461,f144])).

fof(f195,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f5864,plain,
    ( spl6_111
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5426,f435,f5861])).

fof(f435,plain,
    ( spl6_22
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f5426,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f461,f144])).

fof(f437,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f435])).

fof(f5859,plain,
    ( spl6_110
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f5854,f5058,f707,f427,f5856])).

fof(f427,plain,
    ( spl6_21
  <=> m1_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f5854,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5853,f64])).

fof(f5853,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5852,f5060])).

fof(f5852,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5427,f709])).

fof(f5427,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f461,f144])).

fof(f429,plain,
    ( m1_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f427])).

fof(f5848,plain,
    ( spl6_107
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f5430,f140,f5821])).

fof(f5821,plain,
    ( spl6_107
  <=> k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f5430,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f461,f144])).

fof(f5847,plain,
    ( spl6_108
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f5846,f5058,f225,f193,f5829])).

fof(f5829,plain,
    ( spl6_108
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f5846,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5845,f5060])).

fof(f5845,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5844,f1116])).

fof(f5844,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5431,f227])).

fof(f5431,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK0) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f461,f144])).

fof(f5843,plain,
    ( spl6_108
    | ~ spl6_22
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f5842,f5058,f435,f5829])).

fof(f5842,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5841,f5060])).

fof(f5841,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f5432,f1116])).

fof(f5432,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f461,f144])).

fof(f5840,plain,
    ( spl6_109
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5835,f707,f427,f5837])).

fof(f5837,plain,
    ( spl6_109
  <=> k4_subset_1(sK0,sK1,sK0) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f5835,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5834,f709])).

fof(f5834,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f5433,f1116])).

fof(f5433,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f461,f144])).

fof(f5832,plain,
    ( spl6_108
    | ~ spl6_22
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f5827,f5058,f435,f5829])).

fof(f5827,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f5826,f5060])).

fof(f5826,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f5825,f1116])).

fof(f5825,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f5438,f113])).

fof(f5438,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f461,f306])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_subset_1(X2,k4_xboole_0(X0,X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f144,f113])).

fof(f5824,plain,
    ( spl6_107
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5819,f707,f427,f5821])).

fof(f5819,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5818,f709])).

fof(f5818,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5817,f113])).

fof(f5817,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)))
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5439,f709])).

fof(f5439,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f461,f306])).

fof(f5816,plain,
    ( spl6_105
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f5815,f5388,f140,f5766])).

fof(f5766,plain,
    ( spl6_105
  <=> sK1 = k4_subset_1(sK1,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f5388,plain,
    ( spl6_88
  <=> sK1 = k4_subset_1(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f5815,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f5440,f5390])).

fof(f5390,plain,
    ( sK1 = k4_subset_1(sK0,sK1,k1_xboole_0)
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f5388])).

fof(f5440,plain,
    ( k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f178,f178,f142,f461,f309])).

fof(f309,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_subset_1(X2,X0,X1) = k4_subset_1(X3,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f144,f144])).

fof(f5814,plain,
    ( spl6_92
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5813,f4093,f140,f5616])).

fof(f5616,plain,
    ( spl6_92
  <=> sK1 = k4_subset_1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f4093,plain,
    ( spl6_61
  <=> sK1 = k4_subset_1(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f5813,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5441,f4095])).

fof(f4095,plain,
    ( sK1 = k4_subset_1(sK0,sK1,sK1)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f4093])).

fof(f5441,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f461,f142,f461,f309])).

fof(f5812,plain,
    ( spl6_106
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f5811,f5395,f225,f193,f5772])).

fof(f5772,plain,
    ( spl6_106
  <=> k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f5395,plain,
    ( spl6_89
  <=> k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f5811,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_89 ),
    inference(forward_demodulation,[],[f5810,f5397])).

fof(f5397,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f5395])).

fof(f5810,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5442,f227])).

fof(f5442,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k1_xboole_0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f178,f178,f195,f461,f309])).

fof(f5809,plain,
    ( spl6_104
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5808,f225,f193,f5745])).

fof(f5808,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5443,f227])).

fof(f5443,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f461,f195,f461,f309])).

fof(f5807,plain,
    ( spl6_106
    | ~ spl6_22
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f5806,f5395,f435,f5772])).

fof(f5806,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_89 ),
    inference(forward_demodulation,[],[f5444,f5397])).

fof(f5444,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f178,f178,f437,f461,f309])).

fof(f5805,plain,
    ( spl6_104
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5445,f435,f5745])).

fof(f5445,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f461,f437,f461,f309])).

fof(f5804,plain,
    ( spl6_105
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f5803,f5388,f707,f427,f5766])).

fof(f5803,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f5802,f5390])).

fof(f5802,plain,
    ( k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5446,f709])).

fof(f5446,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f178,f178,f429,f461,f309])).

fof(f5801,plain,
    ( spl6_92
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5800,f4093,f707,f427,f5616])).

fof(f5800,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5799,f4095])).

fof(f5799,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5447,f709])).

fof(f5447,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f461,f429,f461,f309])).

fof(f5796,plain,
    ( spl6_102
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f5464,f140,f5729])).

fof(f5729,plain,
    ( spl6_102
  <=> k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f5464,plain,
    ( k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f178,f178,f461,f309])).

fof(f5795,plain,
    ( spl6_103
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5794,f225,f193,f5734])).

fof(f5734,plain,
    ( spl6_103
  <=> k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f5794,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5465,f227])).

fof(f5465,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k1_xboole_0,k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f178,f178,f461,f309])).

fof(f5793,plain,
    ( spl6_103
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5466,f435,f5734])).

fof(f5466,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f178,f178,f461,f309])).

fof(f5792,plain,
    ( spl6_102
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5791,f707,f427,f5729])).

fof(f5791,plain,
    ( k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5467,f709])).

fof(f5467,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f178,f178,f461,f309])).

fof(f5789,plain,
    ( spl6_92
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5788,f4093,f140,f5616])).

fof(f5788,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5472,f4095])).

fof(f5472,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f142,f461,f461,f309])).

fof(f5787,plain,
    ( spl6_104
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5786,f225,f193,f5745])).

fof(f5786,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5473,f227])).

fof(f5473,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f195,f461,f461,f309])).

fof(f5785,plain,
    ( spl6_104
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5474,f435,f5745])).

fof(f5474,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f437,f461,f461,f309])).

fof(f5784,plain,
    ( spl6_92
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5783,f4093,f707,f427,f5616])).

fof(f5783,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5782,f4095])).

fof(f5782,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5475,f709])).

fof(f5475,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f429,f461,f461,f309])).

fof(f5780,plain,
    ( spl6_105
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f5779,f5388,f140,f5766])).

fof(f5779,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f5484,f5390])).

fof(f5484,plain,
    ( k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f178,f178,f461,f309])).

fof(f5778,plain,
    ( spl6_106
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f5777,f5395,f225,f193,f5772])).

fof(f5777,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_89 ),
    inference(forward_demodulation,[],[f5776,f5397])).

fof(f5776,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5485,f227])).

fof(f5485,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k1_xboole_0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f178,f178,f461,f309])).

fof(f5775,plain,
    ( spl6_106
    | ~ spl6_22
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f5770,f5395,f435,f5772])).

fof(f5770,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_89 ),
    inference(forward_demodulation,[],[f5486,f5397])).

fof(f5486,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f178,f178,f461,f309])).

fof(f5769,plain,
    ( spl6_105
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f5764,f5388,f707,f427,f5766])).

fof(f5764,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f5763,f5390])).

fof(f5763,plain,
    ( k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5487,f709])).

fof(f5487,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f178,f178,f461,f309])).

fof(f5761,plain,
    ( spl6_92
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5760,f4093,f140,f5616])).

fof(f5760,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5492,f4095])).

fof(f5492,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f142,f461,f461,f309])).

fof(f5759,plain,
    ( spl6_104
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5758,f225,f193,f5745])).

fof(f5758,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5493,f227])).

fof(f5493,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f195,f461,f461,f309])).

fof(f5757,plain,
    ( spl6_104
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5494,f435,f5745])).

fof(f5494,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f437,f461,f461,f309])).

fof(f5756,plain,
    ( spl6_92
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5755,f4093,f707,f427,f5616])).

fof(f5755,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5754,f4095])).

fof(f5754,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5495,f709])).

fof(f5495,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f429,f461,f461,f309])).

fof(f5752,plain,
    ( spl6_92
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5751,f4093,f140,f5616])).

fof(f5751,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5500,f4095])).

fof(f5500,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f461,f142,f142,f461,f309])).

fof(f5750,plain,
    ( spl6_104
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5749,f225,f193,f5745])).

fof(f5749,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5503,f227])).

fof(f5503,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f461,f195,f461,f309])).

fof(f5748,plain,
    ( spl6_104
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5505,f435,f5745])).

fof(f5505,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f461,f437,f461,f309])).

fof(f5743,plain,
    ( spl6_92
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5742,f4093,f707,f427,f5616])).

fof(f5742,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5741,f4095])).

fof(f5741,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5507,f709])).

fof(f5507,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f461,f429,f461,f309])).

fof(f5740,plain,
    ( spl6_102
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f5508,f140,f5729])).

fof(f5508,plain,
    ( k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f178,f178,f461,f309])).

fof(f5739,plain,
    ( spl6_103
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5738,f225,f193,f5734])).

fof(f5738,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5509,f227])).

fof(f5509,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k1_xboole_0,k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f178,f178,f461,f309])).

fof(f5737,plain,
    ( spl6_103
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5510,f435,f5734])).

fof(f5510,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f178,f178,f461,f309])).

fof(f5732,plain,
    ( spl6_102
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5727,f707,f427,f5729])).

fof(f5727,plain,
    ( k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5511,f709])).

fof(f5511,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f178,f178,f461,f309])).

fof(f5724,plain,
    ( ~ spl6_101
    | spl6_14 ),
    inference(avatar_split_clause,[],[f5520,f329,f5721])).

fof(f5721,plain,
    ( spl6_101
  <=> r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f5520,plain,
    ( ~ r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_xboole_0))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f507,f178,f461,f310])).

fof(f5716,plain,
    ( ~ spl6_99
    | spl6_14 ),
    inference(avatar_split_clause,[],[f5525,f329,f5701])).

fof(f5701,plain,
    ( spl6_99
  <=> r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f5525,plain,
    ( ~ r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f331,f461,f461,f310])).

fof(f5712,plain,
    ( ~ spl6_100
    | spl6_14 ),
    inference(avatar_split_clause,[],[f5530,f329,f5709])).

fof(f5709,plain,
    ( spl6_100
  <=> r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_xboole_0,k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f5530,plain,
    ( ~ r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_xboole_0,k1_zfmisc_1(sK1)))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f507,f178,f461,f310])).

fof(f5704,plain,
    ( ~ spl6_99
    | spl6_14 ),
    inference(avatar_split_clause,[],[f5535,f329,f5701])).

fof(f5535,plain,
    ( ~ r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f331,f461,f461,f310])).

fof(f5696,plain,
    ( spl6_94
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f5541,f387,f5647])).

fof(f5647,plain,
    ( spl6_94
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f387,plain,
    ( spl6_15
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f5541,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f461,f461,f311])).

fof(f311,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(X7,k4_subset_1(X6,X4,X5))
      | ~ r2_hidden(X7,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f149,f144])).

fof(f149,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f129,f114])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f91,f111])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f389,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f387])).

fof(f5695,plain,
    ( spl6_93
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5694,f707,f562,f5639])).

fof(f5639,plain,
    ( spl6_93
  <=> r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f562,plain,
    ( spl6_24
  <=> r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f5694,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5542,f709])).

fof(f5542,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f461,f461,f311])).

fof(f564,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f562])).

fof(f5693,plain,
    ( spl6_93
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f5544,f169,f5639])).

fof(f5544,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f461,f461,f311])).

fof(f5692,plain,
    ( spl6_93
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5691,f805,f5639])).

fof(f5691,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f5548,f1231])).

fof(f5548,plain,
    ( r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f461,f461,f311])).

fof(f5690,plain,
    ( spl6_98
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f5550,f387,f5687])).

fof(f5687,plain,
    ( spl6_98
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f5550,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f178,f461,f311])).

fof(f5685,plain,
    ( spl6_97
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5684,f707,f562,f5679])).

fof(f5679,plain,
    ( spl6_97
  <=> r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f5684,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5551,f709])).

fof(f5551,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f178,f461,f311])).

fof(f5683,plain,
    ( spl6_97
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f5553,f169,f5679])).

fof(f5553,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f178,f461,f311])).

fof(f5682,plain,
    ( spl6_97
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5677,f805,f5679])).

fof(f5677,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f5557,f1231])).

fof(f5557,plain,
    ( r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f178,f461,f311])).

fof(f5676,plain,
    ( spl6_94
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f5559,f387,f5647])).

fof(f5559,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f461,f461,f311])).

fof(f5675,plain,
    ( spl6_93
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5674,f707,f562,f5639])).

fof(f5674,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5560,f709])).

fof(f5560,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f461,f461,f311])).

fof(f5673,plain,
    ( spl6_93
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f5562,f169,f5639])).

fof(f5562,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f461,f461,f311])).

fof(f5672,plain,
    ( spl6_93
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5671,f805,f5639])).

fof(f5671,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f5566,f1231])).

fof(f5566,plain,
    ( r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f461,f461,f311])).

fof(f5670,plain,
    ( spl6_96
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f5568,f387,f5667])).

fof(f5667,plain,
    ( spl6_96
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f5568,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f178,f461,f312])).

fof(f312,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(X11,k4_subset_1(X10,X8,X9))
      | ~ r2_hidden(X11,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X10)) ) ),
    inference(superposition,[],[f148,f144])).

fof(f5665,plain,
    ( spl6_95
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5664,f707,f562,f5659])).

fof(f5659,plain,
    ( spl6_95
  <=> r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f5664,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5569,f709])).

fof(f5569,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f178,f461,f312])).

fof(f5663,plain,
    ( spl6_95
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f5571,f169,f5659])).

fof(f5571,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f178,f461,f312])).

fof(f5662,plain,
    ( spl6_95
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5657,f805,f5659])).

fof(f5657,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f5575,f1231])).

fof(f5575,plain,
    ( r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f178,f461,f312])).

fof(f5656,plain,
    ( spl6_94
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f5577,f387,f5647])).

fof(f5577,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f461,f461,f312])).

fof(f5655,plain,
    ( spl6_93
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5654,f707,f562,f5639])).

fof(f5654,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5578,f709])).

fof(f5578,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f461,f461,f312])).

fof(f5653,plain,
    ( spl6_93
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f5580,f169,f5639])).

fof(f5580,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f461,f461,f312])).

fof(f5652,plain,
    ( spl6_93
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5651,f805,f5639])).

fof(f5651,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f5584,f1231])).

fof(f5584,plain,
    ( r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f461,f461,f312])).

fof(f5650,plain,
    ( spl6_94
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f5586,f387,f5647])).

fof(f5586,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f461,f461,f312])).

fof(f5645,plain,
    ( spl6_93
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5644,f707,f562,f5639])).

fof(f5644,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5587,f709])).

fof(f5587,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f461,f461,f312])).

fof(f5643,plain,
    ( spl6_93
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f5589,f169,f5639])).

fof(f5589,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f461,f461,f312])).

fof(f5642,plain,
    ( spl6_93
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5637,f805,f5639])).

fof(f5637,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f5593,f1231])).

fof(f5593,plain,
    ( r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f461,f461,f312])).

fof(f5619,plain,
    ( spl6_92
    | ~ spl6_13
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f5614,f4093,f314,f5616])).

fof(f314,plain,
    ( spl6_13
  <=> k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f5614,plain,
    ( sK1 = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_13
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f5611,f4095])).

fof(f5611,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f461,f453])).

fof(f453,plain,
    ( ! [X3] :
        ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(X3,sK1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X3)) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( ! [X3] :
        ( k4_subset_1(sK0,sK1,sK1) = k4_subset_1(X3,sK1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X3))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X3)) )
    | ~ spl6_13 ),
    inference(superposition,[],[f316,f144])).

fof(f316,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f314])).

fof(f5420,plain,
    ( spl6_90
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f5334,f140,f5409])).

fof(f5409,plain,
    ( spl6_90
  <=> k4_subset_1(sK0,k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f5334,plain,
    ( k4_subset_1(sK0,k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f178,f144])).

fof(f5419,plain,
    ( spl6_91
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5418,f225,f193,f5414])).

fof(f5414,plain,
    ( spl6_91
  <=> k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f5418,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5335,f227])).

fof(f5335,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k3_subset_1(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f178,f144])).

fof(f5417,plain,
    ( spl6_91
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5336,f435,f5414])).

fof(f5336,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f178,f144])).

fof(f5412,plain,
    ( spl6_90
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5407,f707,f427,f5409])).

fof(f5407,plain,
    ( k4_subset_1(sK0,k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5337,f709])).

fof(f5337,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f178,f144])).

fof(f5405,plain,
    ( spl6_88
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f5404,f140,f5388])).

fof(f5404,plain,
    ( sK1 = k4_subset_1(sK0,sK1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f5403,f64])).

fof(f5403,plain,
    ( k4_subset_1(sK0,sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f5339,f499])).

fof(f5339,plain,
    ( k4_subset_1(sK0,sK1,k1_xboole_0) = k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f178,f144])).

fof(f5402,plain,
    ( spl6_89
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f5401,f225,f193,f5395])).

fof(f5401,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f5400,f227])).

fof(f5400,plain,
    ( k3_subset_1(sK0,sK1) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f5399,f64])).

fof(f5399,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k5_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f5340,f499])).

fof(f5340,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k1_xboole_0,k3_subset_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f178,f144])).

fof(f5398,plain,
    ( spl6_89
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f5393,f435,f5395])).

fof(f5393,plain,
    ( k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f5392,f64])).

fof(f5392,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f5341,f499])).

fof(f5341,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f178,f144])).

fof(f5391,plain,
    ( spl6_88
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5386,f707,f427,f5388])).

fof(f5386,plain,
    ( sK1 = k4_subset_1(sK0,sK1,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f5385,f709])).

fof(f5385,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f5384,f64])).

fof(f5384,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f5342,f499])).

fof(f5342,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f178,f144])).

fof(f5320,plain,
    ( spl6_87
    | ~ spl6_51
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f5315,f5058,f3948,f5317])).

fof(f5317,plain,
    ( spl6_87
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f3948,plain,
    ( spl6_51
  <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f5315,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl6_51
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f3950,f5060])).

fof(f3950,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f3948])).

fof(f5275,plain,
    ( spl6_86
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f4665,f387,f5272])).

fof(f5272,plain,
    ( spl6_86
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f4665,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f507,f131])).

fof(f5270,plain,
    ( spl6_85
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f5269,f707,f562,f5264])).

fof(f5264,plain,
    ( spl6_85
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f5269,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f4666,f709])).

fof(f4666,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f564,f507,f131])).

fof(f5268,plain,
    ( spl6_85
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f4668,f169,f5264])).

fof(f4668,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f507,f131])).

fof(f5267,plain,
    ( spl6_85
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5262,f805,f5264])).

fof(f5262,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4672,f1231])).

fof(f4672,plain,
    ( r2_hidden(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f131])).

fof(f5251,plain,
    ( ~ spl6_84
    | spl6_14 ),
    inference(avatar_split_clause,[],[f4681,f329,f5248])).

fof(f5248,plain,
    ( spl6_84
  <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(sK1),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f4681,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(sK1),k1_xboole_0)))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f507,f150])).

fof(f5229,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4779,f209,f5058])).

fof(f4779,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f78])).

fof(f5228,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4781,f209,f5058])).

fof(f4781,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f78])).

fof(f5227,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5226,f209,f5058])).

fof(f5226,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4783,f499])).

fof(f4783,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f260])).

fof(f260,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK2(X2,k4_xboole_0(X3,X4)),X3)
      | r2_hidden(sK2(X2,k4_xboole_0(X3,X4)),X2)
      | k4_xboole_0(X3,X4) = X2 ) ),
    inference(resolution,[],[f78,f133])).

fof(f5224,plain,
    ( spl6_73
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5223,f209,f5073])).

fof(f5073,plain,
    ( spl6_73
  <=> k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f5223,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4788,f499])).

fof(f4788,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f288])).

fof(f288,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK2(X6,k5_xboole_0(X7,k4_xboole_0(X8,X7))),X8)
      | r2_hidden(sK2(X6,k5_xboole_0(X7,k4_xboole_0(X8,X7))),X7)
      | k5_xboole_0(X7,k4_xboole_0(X8,X7)) = X6
      | r2_hidden(sK2(X6,k5_xboole_0(X7,k4_xboole_0(X8,X7))),X6) ) ),
    inference(resolution,[],[f150,f78])).

fof(f5222,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5221,f209,f5058])).

fof(f5221,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4789,f526])).

fof(f4789,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f288])).

fof(f5220,plain,
    ( spl6_72
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5219,f209,f5065])).

fof(f5065,plain,
    ( spl6_72
  <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f5219,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4791,f1044])).

fof(f1044,plain,
    ( ! [X0] : k4_xboole_0(sK1,sK0) = k4_xboole_0(k4_xboole_0(sK1,sK0),X0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f99])).

fof(f4791,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f288])).

fof(f5218,plain,
    ( spl6_70
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5217,f209,f5051])).

fof(f5051,plain,
    ( spl6_70
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f5217,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4792,f1044])).

fof(f4792,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f288])).

fof(f5216,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5215,f209,f5058])).

fof(f5215,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4793,f526])).

fof(f4793,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f288])).

fof(f5214,plain,
    ( spl6_74
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5213,f209,f5083])).

fof(f5083,plain,
    ( spl6_74
  <=> k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f5213,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4795,f1044])).

fof(f4795,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f288])).

fof(f5212,plain,
    ( spl6_73
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5211,f209,f5073])).

fof(f5211,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4796,f499])).

fof(f4796,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f288])).

fof(f5210,plain,
    ( spl6_70
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5209,f209,f5051])).

fof(f5209,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4797,f1044])).

fof(f4797,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f288])).

fof(f5207,plain,
    ( spl6_73
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5206,f209,f5073])).

fof(f5206,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4800,f499])).

fof(f4800,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f147])).

fof(f5205,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5204,f209,f5058])).

fof(f5204,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4801,f526])).

fof(f4801,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f147])).

fof(f5203,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4804,f209,f5058])).

fof(f4804,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f542,f542,f507,f507,f351])).

fof(f5202,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4805,f209,f5058])).

fof(f4805,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).

fof(f5201,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4808,f209,f5058])).

fof(f4808,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f507,f542,f507,f507,f507,f351])).

fof(f5200,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4809,f209,f5058])).

fof(f4809,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).

fof(f5199,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4812,f209,f5058])).

fof(f4812,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f542,f507,f351])).

fof(f5198,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4814,f209,f5058])).

fof(f4814,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f507,f542,f507,f351])).

fof(f5197,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4815,f209,f5058])).

fof(f4815,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).

fof(f5196,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4817,f209,f5058])).

fof(f4817,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).

fof(f5195,plain,
    ( spl6_83
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4827,f209,f169,f5191])).

fof(f5191,plain,
    ( spl6_83
  <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f4827,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f542,f542,f507,f359])).

fof(f359,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(sK4(X16,X17,X18),X18)
      | ~ r2_hidden(X19,X16)
      | r2_hidden(sK4(X16,X17,X18),X17)
      | r2_hidden(sK4(X16,X17,X18),X16)
      | r2_hidden(X19,X18) ) ),
    inference(superposition,[],[f149,f147])).

fof(f5194,plain,
    ( spl6_83
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5189,f805,f209,f5191])).

fof(f5189,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4831,f1231])).

fof(f4831,plain,
    ( r2_hidden(sK4(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f542,f542,f507,f359])).

fof(f5187,plain,
    ( spl6_82
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4849,f209,f169,f5183])).

fof(f5183,plain,
    ( spl6_82
  <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f4849,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f507,f542,f542,f507,f360])).

fof(f360,plain,(
    ! [X23,X21,X22,X20] :
      ( r2_hidden(sK4(X20,X21,X22),X22)
      | r2_hidden(X23,X21)
      | r2_hidden(X23,X20)
      | r2_hidden(sK4(X20,X21,X22),X21)
      | r2_hidden(sK4(X20,X21,X22),X20)
      | ~ r2_hidden(X23,X22) ) ),
    inference(superposition,[],[f150,f147])).

fof(f5186,plain,
    ( spl6_82
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5181,f805,f209,f5183])).

fof(f5181,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4853,f1231])).

fof(f4853,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f542,f542,f507,f360])).

fof(f5179,plain,
    ( spl6_72
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5178,f209,f5065])).

fof(f5178,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4867,f1044])).

fof(f4867,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f147])).

fof(f5177,plain,
    ( spl6_70
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5176,f209,f5051])).

fof(f5176,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4868,f1044])).

fof(f4868,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f147])).

fof(f5175,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5174,f209,f5058])).

fof(f5174,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4869,f526])).

fof(f4869,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f147])).

fof(f5173,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4872,f209,f5058])).

fof(f4872,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f542,f542,f507,f351])).

fof(f5172,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4873,f209,f5058])).

fof(f4873,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).

fof(f5171,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4876,f209,f5058])).

fof(f4876,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f507,f507,f507,f351])).

fof(f5170,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4877,f209,f5058])).

fof(f4877,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).

fof(f5169,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4880,f209,f5058])).

fof(f4880,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f542,f507,f351])).

fof(f5168,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4881,f209,f5058])).

fof(f4881,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).

fof(f5167,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4884,f209,f5058])).

fof(f4884,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f507,f507,f542,f507,f507,f351])).

fof(f5166,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4885,f209,f5058])).

fof(f4885,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).

fof(f5165,plain,
    ( spl6_81
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4891,f209,f169,f5161])).

fof(f5161,plain,
    ( spl6_81
  <=> r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f4891,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f542,f542,f507,f358])).

fof(f358,plain,(
    ! [X14,X12,X15,X13] :
      ( r2_hidden(sK4(X12,X13,X14),X14)
      | ~ r2_hidden(X15,X13)
      | r2_hidden(sK4(X12,X13,X14),X13)
      | r2_hidden(sK4(X12,X13,X14),X12)
      | r2_hidden(X15,X14) ) ),
    inference(superposition,[],[f148,f147])).

fof(f5164,plain,
    ( spl6_81
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5159,f805,f209,f5161])).

fof(f5159,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4895,f1231])).

fof(f4895,plain,
    ( r2_hidden(sK4(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k4_xboole_0(sK1,sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f542,f542,f507,f358])).

fof(f5157,plain,
    ( spl6_80
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4917,f209,f169,f5153])).

fof(f5153,plain,
    ( spl6_80
  <=> r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f4917,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f507,f542,f542,f507,f360])).

fof(f5156,plain,
    ( spl6_80
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5151,f805,f209,f5153])).

fof(f5151,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4921,f1231])).

fof(f4921,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f542,f542,f507,f360])).

fof(f5150,plain,
    ( spl6_79
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f4928,f169,f5146])).

fof(f5146,plain,
    ( spl6_79
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f4928,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f507,f507,f507,f507,f360])).

fof(f5149,plain,
    ( spl6_79
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5144,f805,f5146])).

fof(f5144,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4932,f1231])).

fof(f4932,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f507,f507,f507,f360])).

fof(f5143,plain,
    ( spl6_74
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5142,f209,f5083])).

fof(f5142,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4935,f1044])).

fof(f4935,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f147])).

fof(f5141,plain,
    ( spl6_73
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5140,f209,f5073])).

fof(f5140,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4936,f499])).

fof(f4936,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f147])).

fof(f5139,plain,
    ( spl6_70
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5138,f209,f5051])).

fof(f5138,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f4937,f1044])).

fof(f4937,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f147])).

fof(f5137,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4939,f209,f5058])).

fof(f4939,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f542,f542,f542,f507,f351])).

fof(f5136,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4941,f209,f5058])).

fof(f4941,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).

fof(f5135,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4943,f209,f5058])).

fof(f4943,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).

fof(f5134,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4945,f209,f5058])).

fof(f4945,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).

fof(f5133,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4947,f209,f5058])).

fof(f4947,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f542,f542,f542,f507,f351])).

fof(f5132,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4949,f209,f5058])).

fof(f4949,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).

fof(f5131,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4951,f209,f5058])).

fof(f4951,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).

fof(f5130,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4953,f209,f5058])).

fof(f4953,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).

fof(f5129,plain,
    ( spl6_78
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4959,f209,f169,f5125])).

fof(f5125,plain,
    ( spl6_78
  <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f4959,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f507,f542,f507,f358])).

fof(f5128,plain,
    ( spl6_78
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5123,f805,f209,f5125])).

fof(f5123,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4963,f1231])).

fof(f4963,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f542,f507,f358])).

fof(f5122,plain,
    ( spl6_77
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f4968,f169,f5118])).

fof(f5118,plain,
    ( spl6_77
  <=> r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f4968,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f507,f507,f507,f358])).

fof(f5121,plain,
    ( spl6_77
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5116,f805,f5118])).

fof(f5116,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4972,f1231])).

fof(f4972,plain,
    ( r2_hidden(sK4(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f507,f507,f358])).

fof(f5115,plain,
    ( spl6_76
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f4981,f209,f169,f5111])).

fof(f5111,plain,
    ( spl6_76
  <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f4981,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f507,f542,f507,f359])).

fof(f5114,plain,
    ( spl6_76
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5109,f805,f209,f5111])).

fof(f5109,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4985,f1231])).

fof(f4985,plain,
    ( r2_hidden(sK4(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k4_xboole_0(sK1,sK0),k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_7
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f542,f507,f359])).

fof(f5108,plain,
    ( spl6_75
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f4992,f169,f5104])).

fof(f5104,plain,
    ( spl6_75
  <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f4992,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f507,f507,f507,f359])).

fof(f5107,plain,
    ( spl6_75
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f5102,f805,f5104])).

fof(f5102,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f4996,f1231])).

fof(f4996,plain,
    ( r2_hidden(sK4(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0,k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f807,f507,f507,f507,f359])).

fof(f5101,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5100,f209,f5058])).

fof(f5100,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5006,f499])).

fof(f5006,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f99])).

fof(f5093,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5092,f209,f5058])).

fof(f5092,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5091,f526])).

fof(f5091,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5013,f1044])).

fof(f5013,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK1,sK0),X0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f299])).

fof(f5090,plain,
    ( spl6_73
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5089,f209,f5073])).

fof(f5089,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5088,f499])).

fof(f5088,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5014,f499])).

fof(f5014,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f299])).

fof(f5086,plain,
    ( spl6_74
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5081,f209,f5083])).

fof(f5081,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5080,f499])).

fof(f5080,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5016,f1044])).

fof(f5016,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f299])).

fof(f5079,plain,
    ( spl6_70
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5078,f209,f5051])).

fof(f5078,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5077,f499])).

fof(f5077,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5017,f1044])).

fof(f5017,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f299])).

fof(f5076,plain,
    ( spl6_73
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5071,f209,f5073])).

fof(f5071,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5070,f499])).

fof(f5070,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5018,f499])).

fof(f5018,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f299])).

fof(f5068,plain,
    ( spl6_72
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5063,f209,f5065])).

fof(f5063,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5062,f1044])).

fof(f5062,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK0),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5020,f1044])).

fof(f5020,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(sK1,sK0),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f542,f507,f299])).

fof(f5061,plain,
    ( spl6_71
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5056,f209,f5058])).

fof(f5056,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5055,f526])).

fof(f5055,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5021,f1044])).

fof(f5021,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK1,sK0),X0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f507,f542,f507,f299])).

fof(f5054,plain,
    ( spl6_70
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f5049,f209,f5051])).

fof(f5049,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5048,f499])).

fof(f5048,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f5022,f1044])).

fof(f5022,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f542,f507,f507,f299])).

fof(f4642,plain,
    ( ~ spl6_69
    | spl6_63 ),
    inference(avatar_split_clause,[],[f4637,f4120,f4639])).

fof(f4639,plain,
    ( spl6_69
  <=> r2_hidden(sK0,k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f4120,plain,
    ( spl6_63
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f4637,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | spl6_63 ),
    inference(unit_resulting_resolution,[],[f4122,f127])).

fof(f4122,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | spl6_63 ),
    inference(avatar_component_clause,[],[f4120])).

fof(f4531,plain,
    ( ~ spl6_67
    | spl6_68
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f4522,f4100,f419,f4528,f4524])).

fof(f4522,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_20
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f4521,f4102])).

fof(f4521,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f4503,f525])).

fof(f4503,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))
    | ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl6_20 ),
    inference(superposition,[],[f421,f235])).

fof(f4426,plain,(
    spl6_47 ),
    inference(avatar_contradiction_clause,[],[f4422])).

fof(f4422,plain,
    ( $false
    | spl6_47 ),
    inference(unit_resulting_resolution,[],[f161,f3930,f127])).

fof(f3930,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl6_47 ),
    inference(avatar_component_clause,[],[f3928])).

fof(f4425,plain,(
    spl6_47 ),
    inference(avatar_contradiction_clause,[],[f4420])).

fof(f4420,plain,
    ( $false
    | spl6_47 ),
    inference(unit_resulting_resolution,[],[f124,f3930])).

fof(f4424,plain,(
    spl6_47 ),
    inference(avatar_contradiction_clause,[],[f4423])).

fof(f4423,plain,
    ( $false
    | spl6_47 ),
    inference(resolution,[],[f3930,f124])).

fof(f4356,plain,
    ( ~ spl6_2
    | spl6_66
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f4278,f314,f4353,f140])).

fof(f4353,plain,
    ( spl6_66
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k4_subset_1(X0,sK1,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f4278,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_subset_1(X2,sK1,sK1))
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f4277])).

fof(f4277,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_subset_1(X2,sK1,sK1))
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | ~ spl6_13 ),
    inference(superposition,[],[f450,f309])).

fof(f450,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k4_subset_1(sK0,sK1,sK1))
        | r2_hidden(X6,sK1) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k4_subset_1(sK0,sK1,sK1))
        | r2_hidden(X6,sK1)
        | r2_hidden(X6,sK1) )
    | ~ spl6_13 ),
    inference(superposition,[],[f150,f316])).

fof(f4355,plain,
    ( ~ spl6_2
    | spl6_66
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f4279,f314,f4353,f140])).

fof(f4279,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k4_subset_1(X0,sK1,sK1))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f4276])).

fof(f4276,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k4_subset_1(X0,sK1,sK1))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl6_13 ),
    inference(superposition,[],[f450,f309])).

fof(f4249,plain,
    ( ~ spl6_2
    | spl6_65
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f4193,f314,f4246,f140])).

fof(f4246,plain,
    ( spl6_65
  <=> ! [X1,X0] :
        ( r2_hidden(X1,k4_subset_1(X0,sK1,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f4193,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X3,k4_subset_1(X2,sK1,sK1))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f4192])).

fof(f4192,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X3,k4_subset_1(X2,sK1,sK1))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | ~ spl6_13 ),
    inference(superposition,[],[f447,f309])).

fof(f447,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k4_subset_1(sK0,sK1,sK1))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl6_13 ),
    inference(superposition,[],[f148,f316])).

fof(f4248,plain,
    ( ~ spl6_2
    | spl6_65
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f4194,f314,f4246,f140])).

fof(f4194,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k4_subset_1(X0,sK1,sK1))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f4191])).

fof(f4191,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k4_subset_1(X0,sK1,sK1))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl6_13 ),
    inference(superposition,[],[f447,f309])).

fof(f4127,plain,
    ( ~ spl6_63
    | spl6_64
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f4118,f427,f4124,f4120])).

fof(f4124,plain,
    ( spl6_64
  <=> m1_subset_1(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f4118,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f4086,f525])).

fof(f4086,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_21 ),
    inference(superposition,[],[f429,f235])).

fof(f4111,plain,
    ( spl6_61
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f4110,f707,f427,f4093])).

fof(f4110,plain,
    ( sK1 = k4_subset_1(sK0,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f4109,f709])).

fof(f4109,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f4058,f526])).

fof(f4058,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f429,f144])).

fof(f4107,plain,
    ( spl6_62
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f4106,f707,f427,f225,f193,f4100])).

fof(f4106,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f4105,f709])).

fof(f4105,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f4104,f370])).

fof(f370,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X4,X5)) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X5)),k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f116,f114])).

fof(f4104,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f4060,f227])).

fof(f4060,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1)))
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f195,f429,f144])).

fof(f4103,plain,
    ( spl6_62
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f4098,f707,f435,f427,f4100])).

fof(f4098,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f4097,f709])).

fof(f4097,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f4061,f370])).

fof(f4061,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f437,f429,f144])).

fof(f4096,plain,
    ( spl6_61
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f4091,f707,f427,f4093])).

fof(f4091,plain,
    ( sK1 = k4_subset_1(sK0,sK1,sK1)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f4090,f709])).

fof(f4090,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f4062,f526])).

fof(f4062,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f429,f429,f144])).

fof(f4050,plain,
    ( spl6_59
    | spl6_60
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f4042,f707,f273,f209,f4047,f4044])).

fof(f4044,plain,
    ( spl6_59
  <=> ! [X88] : ~ r1_tarski(sK1,X88) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f4047,plain,
    ( spl6_60
  <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f273,plain,
    ( spl6_10
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f4042,plain,
    ( ! [X88] :
        ( sK1 = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1))
        | ~ r1_tarski(sK1,X88) )
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f4041,f709])).

fof(f4041,plain,
    ( ! [X88] :
        ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1))
        | ~ r1_tarski(sK1,X88) )
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f4040,f113])).

fof(f4040,plain,
    ( ! [X88] :
        ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1))
        | ~ r1_tarski(sK1,X88) )
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3895,f1044])).

fof(f3895,plain,
    ( ! [X88] :
        ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,X88)))
        | ~ r1_tarski(sK1,X88) )
    | ~ spl6_10 ),
    inference(superposition,[],[f373,f275])).

fof(f275,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f273])).

fof(f4034,plain,
    ( spl6_58
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f4029,f273,f209,f4031])).

fof(f4031,plain,
    ( spl6_58
  <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f4029,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f4028,f1044])).

fof(f4028,plain,
    ( ! [X81] : k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X81,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f4027,f529])).

fof(f529,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X12,X12))) = k3_tarski(k6_enumset1(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X12))) ),
    inference(superposition,[],[f116,f199])).

fof(f4027,plain,
    ( ! [X81] : k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X81,sK1)) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3890,f1044])).

fof(f3890,plain,
    ( ! [X81] : k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X81,sK1)) = k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(sK1,sK1)))
    | ~ spl6_10 ),
    inference(superposition,[],[f367,f275])).

fof(f4020,plain,
    ( spl6_57
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f4015,f273,f209,f4017])).

fof(f4017,plain,
    ( spl6_57
  <=> k4_xboole_0(sK1,sK0) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f4015,plain,
    ( k4_xboole_0(sK1,sK0) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f4014,f1044])).

fof(f4014,plain,
    ( ! [X77] : k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),X77)) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3886,f1044])).

fof(f3886,plain,
    ( ! [X77] : k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),X77)) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),X77))))
    | ~ spl6_10 ),
    inference(superposition,[],[f361,f275])).

fof(f4013,plain,
    ( ~ spl6_43
    | spl6_56
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f4009,f273,f4011,f3904])).

fof(f4011,plain,
    ( spl6_56
  <=> ! [X76] :
        ( k4_xboole_0(sK1,sK1) = X76
        | r2_hidden(sK4(sK1,sK1,X76),X76)
        | r2_hidden(sK4(sK1,sK1,X76),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f4009,plain,
    ( ! [X76] :
        ( k4_xboole_0(sK1,sK1) = X76
        | r2_hidden(sK4(sK1,sK1,X76),sK1)
        | r2_hidden(sK4(sK1,sK1,X76),X76)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3897,f525])).

fof(f3897,plain,
    ( ! [X76] :
        ( r2_hidden(sK4(sK1,sK1,X76),sK1)
        | k5_xboole_0(sK1,sK1) = X76
        | r2_hidden(sK4(sK1,sK1,X76),X76)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f3885])).

fof(f3885,plain,
    ( ! [X76] :
        ( r2_hidden(sK4(sK1,sK1,X76),sK1)
        | r2_hidden(sK4(sK1,sK1,X76),sK1)
        | k5_xboole_0(sK1,sK1) = X76
        | r2_hidden(sK4(sK1,sK1,X76),X76)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(superposition,[],[f350,f275])).

fof(f350,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),k4_xboole_0(X6,X7))
      | r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X6)
      | k5_xboole_0(k4_xboole_0(X6,X7),X6) = X8
      | r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f147,f115])).

fof(f3995,plain,
    ( ~ spl6_43
    | spl6_55
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3991,f273,f3993,f3904])).

fof(f3993,plain,
    ( spl6_55
  <=> ! [X65] :
        ( k4_xboole_0(sK1,sK1) = X65
        | ~ r2_hidden(sK4(sK1,sK1,X65),sK1)
        | ~ r2_hidden(sK4(sK1,sK1,X65),X65) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f3991,plain,
    ( ! [X65] :
        ( k4_xboole_0(sK1,sK1) = X65
        | ~ r2_hidden(sK4(sK1,sK1,X65),X65)
        | ~ r2_hidden(sK4(sK1,sK1,X65),sK1)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3877,f525])).

fof(f3877,plain,
    ( ! [X65] :
        ( ~ r2_hidden(sK4(sK1,sK1,X65),X65)
        | ~ r2_hidden(sK4(sK1,sK1,X65),sK1)
        | k5_xboole_0(sK1,sK1) = X65
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(superposition,[],[f320,f275])).

fof(f320,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X8)
      | ~ r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X6)
      | k5_xboole_0(k4_xboole_0(X6,X7),X6) = X8
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f145,f115])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f118,f114])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f95,f111])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3987,plain,
    ( ~ spl6_43
    | spl6_54
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3983,f273,f3985,f3904])).

fof(f3985,plain,
    ( spl6_54
  <=> ! [X62] :
        ( k4_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X62)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f3983,plain,
    ( ! [X62] :
        ( k4_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X62))
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3899,f525])).

fof(f3899,plain,
    ( ! [X62] :
        ( k5_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X62))
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f3874])).

fof(f3874,plain,
    ( ! [X62] :
        ( k5_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X62))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X62))
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(superposition,[],[f308,f275])).

fof(f308,plain,(
    ! [X6,X8,X7] :
      ( k5_xboole_0(k4_xboole_0(X6,X7),X6) = k4_subset_1(X8,k4_xboole_0(X6,X7),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8))
      | ~ m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(X8))
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f144,f115])).

fof(f3963,plain,
    ( spl6_53
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3958,f273,f209,f3960])).

fof(f3960,plain,
    ( spl6_53
  <=> k4_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f3958,plain,
    ( k4_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3848,f1044])).

fof(f3848,plain,
    ( k4_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)))
    | ~ spl6_10 ),
    inference(superposition,[],[f240,f275])).

fof(f240,plain,(
    ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ),
    inference(superposition,[],[f112,f113])).

fof(f3957,plain,
    ( spl6_52
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3952,f273,f209,f3954])).

fof(f3954,plain,
    ( spl6_52
  <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f3952,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3847,f1044])).

fof(f3847,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1))
    | ~ spl6_10 ),
    inference(superposition,[],[f238,f275])).

fof(f3951,plain,
    ( ~ spl6_50
    | spl6_51
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3846,f273,f3948,f3944])).

fof(f3846,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl6_10 ),
    inference(superposition,[],[f236,f275])).

fof(f3942,plain,
    ( ~ spl6_43
    | spl6_44
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3941,f273,f3908,f3904])).

fof(f3941,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3845,f525])).

fof(f3845,plain,
    ( sK1 = k5_xboole_0(sK1,sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(superposition,[],[f235,f275])).

fof(f3940,plain,
    ( ~ spl6_43
    | spl6_49
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3936,f273,f3938,f3904])).

fof(f3938,plain,
    ( spl6_49
  <=> ! [X31] :
        ( r2_hidden(X31,k4_xboole_0(sK1,sK1))
        | ~ r2_hidden(X31,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f3936,plain,
    ( ! [X31] :
        ( r2_hidden(X31,k4_xboole_0(sK1,sK1))
        | ~ r2_hidden(X31,sK1)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3843,f525])).

fof(f3843,plain,
    ( ! [X31] :
        ( r2_hidden(X31,k5_xboole_0(sK1,sK1))
        | ~ r2_hidden(X31,sK1)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(superposition,[],[f216,f275])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(k4_xboole_0(X0,X1),X0))
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f148,f115])).

fof(f3935,plain,
    ( ~ spl6_43
    | spl6_48
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3842,f273,f3933,f3904])).

fof(f3933,plain,
    ( spl6_48
  <=> ! [X30] : ~ r2_hidden(X30,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f3842,plain,
    ( ! [X30] :
        ( ~ r2_hidden(X30,sK1)
        | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0)) )
    | ~ spl6_10 ),
    inference(superposition,[],[f203,f275])).

fof(f3931,plain,
    ( ~ spl6_43
    | spl6_44
    | ~ spl6_47
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3841,f273,f3928,f3908,f3904])).

fof(f3841,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = k4_xboole_0(sK1,sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(superposition,[],[f200,f275])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X0,X1))
      | k4_xboole_0(X0,X0) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f115,f115])).

fof(f3923,plain,
    ( ~ spl6_43
    | spl6_44
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3828,f273,f3908,f3904])).

fof(f3828,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(superposition,[],[f115,f275])).

fof(f3921,plain,
    ( spl6_46
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3808,f273,f3918])).

fof(f3918,plain,
    ( spl6_46
  <=> sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f3808,plain,
    ( sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(superposition,[],[f240,f275])).

fof(f3916,plain,
    ( spl6_45
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3807,f273,f3913])).

fof(f3913,plain,
    ( spl6_45
  <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f3807,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl6_10 ),
    inference(superposition,[],[f238,f275])).

fof(f3911,plain,
    ( ~ spl6_43
    | spl6_44
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f3902,f273,f3908,f3904])).

fof(f3902,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f3801,f525])).

fof(f3801,plain,
    ( sK1 = k5_xboole_0(sK1,sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_10 ),
    inference(superposition,[],[f275,f235])).

fof(f2779,plain,
    ( spl6_42
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f2744,f209,f169,f2776])).

fof(f2776,plain,
    ( spl6_42
  <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2744,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f542,f542,f542,f542,f360])).

fof(f2409,plain,
    ( ~ spl6_2
    | ~ spl6_22
    | spl6_41
    | spl6_9 ),
    inference(avatar_split_clause,[],[f2373,f230,f2401,f435,f140])).

fof(f2401,plain,
    ( spl6_41
  <=> ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f230,plain,
    ( spl6_9
  <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2373,plain,
    ( ! [X1] :
        ( sK0 != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) )
    | spl6_9 ),
    inference(superposition,[],[f232,f309])).

fof(f232,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f230])).

fof(f2408,plain,
    ( ~ spl6_2
    | ~ spl6_22
    | spl6_41
    | spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f2407,f225,f153,f2401,f435,f140])).

fof(f153,plain,
    ( spl6_3
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2407,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
        | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl6_3
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2406,f227])).

fof(f2406,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
        | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl6_3
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2405,f227])).

fof(f2405,plain,
    ( ! [X0] :
        ( sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl6_3
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2372,f227])).

fof(f2372,plain,
    ( ! [X0] :
        ( sK0 != k4_subset_1(X0,sK1,k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl6_3 ),
    inference(superposition,[],[f155,f309])).

fof(f155,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2404,plain,
    ( ~ spl6_2
    | ~ spl6_22
    | spl6_41
    | spl6_9 ),
    inference(avatar_split_clause,[],[f2366,f230,f2401,f435,f140])).

fof(f2366,plain,
    ( ! [X1] :
        ( sK0 != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | spl6_9 ),
    inference(superposition,[],[f232,f309])).

fof(f2403,plain,
    ( ~ spl6_2
    | spl6_41
    | ~ spl6_22
    | spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f2399,f225,f153,f435,f2401,f140])).

fof(f2399,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | spl6_3
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2398,f227])).

fof(f2398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | spl6_3
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2397,f227])).

fof(f2397,plain,
    ( ! [X0] :
        ( sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | spl6_3
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f2365,f227])).

fof(f2365,plain,
    ( ! [X0] :
        ( sK0 != k4_subset_1(X0,sK1,k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) )
    | spl6_3 ),
    inference(superposition,[],[f155,f309])).

fof(f2229,plain,
    ( spl6_40
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f2211,f1747,f2226])).

fof(f2226,plain,
    ( spl6_40
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f2211,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f1749,f115])).

fof(f2224,plain,
    ( spl6_39
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f2214,f1747,f2221])).

fof(f2221,plain,
    ( spl6_39
  <=> k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f2214,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f1749,f235])).

fof(f2210,plain,
    ( spl6_38
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f2184,f209,f169,f2207])).

fof(f2207,plain,
    ( spl6_38
  <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f2184,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f542,f542,f542,f359])).

fof(f2180,plain,
    ( spl6_37
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f2154,f209,f169,f2177])).

fof(f2177,plain,
    ( spl6_37
  <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f2154,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f542,f542,f542,f358])).

fof(f1751,plain,
    ( spl6_36
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f1739,f387,f1747])).

fof(f1739,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f389,f127])).

fof(f1750,plain,
    ( spl6_36
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f1731,f387,f1747])).

fof(f1731,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f389,f127])).

fof(f1745,plain,
    ( spl6_35
    | ~ spl6_7
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f1733,f387,f209,f1742])).

fof(f1742,plain,
    ( spl6_35
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1733,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f542,f389,f131])).

fof(f1384,plain,
    ( spl6_34
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f1365,f169,f1381])).

fof(f1381,plain,
    ( spl6_34
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1365,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f161,f205,f256])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | r2_hidden(X2,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f131,f113])).

fof(f1071,plain,
    ( spl6_33
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f1028,f209,f169,f1068])).

fof(f1068,plain,
    ( spl6_33
  <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1028,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f542,f131])).

fof(f1065,plain,
    ( ~ spl6_32
    | ~ spl6_7
    | spl6_14 ),
    inference(avatar_split_clause,[],[f1060,f329,f209,f1062])).

fof(f1062,plain,
    ( spl6_32
  <=> r2_hidden(sK0,k5_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1060,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_7
    | spl6_14 ),
    inference(forward_demodulation,[],[f1031,f1044])).

fof(f1031,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK1))))
    | ~ spl6_7
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f542,f150])).

fof(f1058,plain,
    ( ~ spl6_31
    | ~ spl6_7
    | spl6_14 ),
    inference(avatar_split_clause,[],[f1033,f329,f209,f1055])).

fof(f1055,plain,
    ( spl6_31
  <=> r2_hidden(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1033,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0))))
    | ~ spl6_7
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f331,f542,f150])).

fof(f830,plain,
    ( ~ spl6_30
    | spl6_14 ),
    inference(avatar_split_clause,[],[f810,f329,f827])).

fof(f827,plain,
    ( spl6_30
  <=> r2_hidden(sK0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f810,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1)))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f124,f331,f292])).

fof(f292,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k5_xboole_0(k4_xboole_0(X6,X7),X6))
      | r2_hidden(X8,X6)
      | ~ r1_tarski(X6,X7) ) ),
    inference(global_subsumption,[],[f133,f291])).

fof(f291,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k5_xboole_0(k4_xboole_0(X6,X7),X6))
      | r2_hidden(X8,X6)
      | r2_hidden(X8,k4_xboole_0(X6,X7))
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f150,f115])).

fof(f808,plain,
    ( spl6_29
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f793,f169,f805])).

fof(f793,plain,
    ( r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f124,f171,f216])).

fof(f710,plain,
    ( spl6_28
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f675,f209,f707])).

fof(f675,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f211,f236])).

fof(f670,plain,
    ( spl6_27
    | spl6_14 ),
    inference(avatar_split_clause,[],[f657,f329,f667])).

fof(f667,plain,
    ( spl6_27
  <=> r2_hidden(sK0,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f657,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f161,f331,f131])).

fof(f665,plain,
    ( ~ spl6_26
    | spl6_14 ),
    inference(avatar_split_clause,[],[f659,f329,f662])).

fof(f662,plain,
    ( spl6_26
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f659,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f61,f331,f71])).

fof(f616,plain,
    ( spl6_25
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f578,f209,f613])).

fof(f613,plain,
    ( spl6_25
  <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f578,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f211,f235])).

fof(f565,plain,
    ( spl6_24
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f560,f399,f225,f193,f562])).

fof(f399,plain,
    ( spl6_17
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f560,plain,
    ( r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f559,f401])).

fof(f401,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f399])).

fof(f559,plain,
    ( r2_hidden(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f554,f227])).

fof(f554,plain,
    ( r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(global_subsumption,[],[f61,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f76,f71])).

fof(f498,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f497,f493])).

fof(f493,plain,
    ( spl6_23
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f497,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(global_subsumption,[],[f468])).

fof(f468,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f198,f198])).

fof(f496,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f468,f493])).

fof(f438,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f431,f225,f193,f435])).

fof(f431,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(superposition,[],[f195,f227])).

fof(f430,plain,
    ( spl6_21
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f425,f399,f393,f427])).

fof(f393,plain,
    ( spl6_16
  <=> m1_subset_1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f425,plain,
    ( m1_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f395,f401])).

fof(f395,plain,
    ( m1_subset_1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f393])).

fof(f424,plain,
    ( spl6_5
    | spl6_15
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f423,f225,f193,f387,f174])).

fof(f174,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f423,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f382,f227])).

fof(f382,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(resolution,[],[f195,f71])).

fof(f422,plain,
    ( spl6_20
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f417,f225,f193,f140,f419])).

fof(f417,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f375,f227])).

fof(f375,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f142,f195,f144])).

fof(f416,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f415,f225,f193,f405])).

fof(f405,plain,
    ( spl6_18
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f415,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f376,f227])).

fof(f376,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f195,f144])).

fof(f414,plain,
    ( spl6_19
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f409,f225,f193,f140,f411])).

fof(f409,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f377,f227])).

fof(f377,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,sK1),sK1))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f142,f195,f144])).

fof(f408,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f403,f225,f193,f405])).

fof(f403,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f378,f227])).

fof(f378,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f195,f144])).

fof(f402,plain,
    ( spl6_17
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f397,f225,f193,f399])).

fof(f397,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f379,f227])).

fof(f379,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f77])).

fof(f396,plain,
    ( spl6_16
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f391,f225,f193,f393])).

fof(f391,plain,
    ( m1_subset_1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f380,f227])).

fof(f380,plain,
    ( m1_subset_1(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f195,f76])).

fof(f390,plain,
    ( spl6_15
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f385,f225,f193,f387])).

fof(f385,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f381,f227])).

fof(f381,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f61,f195,f71])).

fof(f332,plain,
    ( ~ spl6_14
    | spl6_11 ),
    inference(avatar_split_clause,[],[f327,f278,f329])).

fof(f278,plain,
    ( spl6_11
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f327,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f280,f127])).

fof(f280,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f278])).

fof(f317,plain,
    ( spl6_13
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f305,f140,f314])).

fof(f305,plain,
    ( k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f142,f144])).

fof(f285,plain,
    ( ~ spl6_11
    | spl6_12
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f271,f209,f282,f278])).

fof(f282,plain,
    ( spl6_12
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f271,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f211,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f276,plain,
    ( spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f269,f209,f273])).

fof(f269,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f211,f115])).

fof(f233,plain,
    ( ~ spl6_2
    | ~ spl6_9
    | spl6_3 ),
    inference(avatar_split_clause,[],[f221,f153,f230,f140])).

fof(f221,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl6_3 ),
    inference(superposition,[],[f155,f77])).

fof(f228,plain,
    ( spl6_8
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f220,f140,f225])).

fof(f220,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f77])).

fof(f213,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f207,f169,f209])).

fof(f207,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f171,f127])).

fof(f212,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f204,f169,f209])).

fof(f204,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f171,f127])).

fof(f196,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f189,f140,f193])).

fof(f189,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f76])).

fof(f177,plain,
    ( spl6_5
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f166,f140,f169,f174])).

fof(f166,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f142])).

fof(f172,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f165,f140,f169])).

fof(f165,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f61,f142,f71])).

fof(f156,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f151,f135,f153])).

fof(f135,plain,
    ( spl6_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f151,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl6_1 ),
    inference(forward_demodulation,[],[f137,f63])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f137,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f143,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f59,f140])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f138,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f60,f135])).

fof(f60,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (24537)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (24553)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (24545)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (24544)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (24532)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (24553)Refutation not found, incomplete strategy% (24553)------------------------------
% 0.22/0.52  % (24553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24553)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24553)Memory used [KB]: 10746
% 0.22/0.52  % (24553)Time elapsed: 0.116 s
% 0.22/0.52  % (24553)------------------------------
% 0.22/0.52  % (24553)------------------------------
% 0.22/0.53  % (24538)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (24554)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (24552)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (24534)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (24556)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (24535)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (24557)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (24536)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (24533)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (24531)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (24548)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (24548)Refutation not found, incomplete strategy% (24548)------------------------------
% 0.22/0.54  % (24548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24548)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24548)Memory used [KB]: 10618
% 0.22/0.54  % (24548)Time elapsed: 0.138 s
% 0.22/0.54  % (24548)------------------------------
% 0.22/0.54  % (24548)------------------------------
% 0.22/0.54  % (24558)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (24559)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (24546)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (24549)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (24550)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (24551)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (24560)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (24541)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (24542)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (24543)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % (24540)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.58  % (24555)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.59  % (24547)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.68/0.60  % (24539)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.22/0.69  % (24564)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.15/0.78  % (24575)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.15/0.82  % (24536)Time limit reached!
% 3.15/0.82  % (24536)------------------------------
% 3.15/0.82  % (24536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.82  % (24536)Termination reason: Time limit
% 3.15/0.82  % (24536)Termination phase: Saturation
% 3.15/0.82  
% 3.15/0.82  % (24536)Memory used [KB]: 8315
% 3.15/0.82  % (24536)Time elapsed: 0.400 s
% 3.15/0.82  % (24536)------------------------------
% 3.15/0.82  % (24536)------------------------------
% 3.98/0.90  % (24541)Time limit reached!
% 3.98/0.90  % (24541)------------------------------
% 3.98/0.90  % (24541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (24541)Termination reason: Time limit
% 3.98/0.92  % (24541)Termination phase: Saturation
% 3.98/0.92  
% 3.98/0.92  % (24541)Memory used [KB]: 12409
% 3.98/0.92  % (24541)Time elapsed: 0.500 s
% 3.98/0.92  % (24541)------------------------------
% 3.98/0.92  % (24541)------------------------------
% 3.98/0.92  % (24532)Time limit reached!
% 3.98/0.92  % (24532)------------------------------
% 3.98/0.92  % (24532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (24543)Time limit reached!
% 3.98/0.92  % (24543)------------------------------
% 3.98/0.92  % (24543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (24543)Termination reason: Time limit
% 3.98/0.92  % (24543)Termination phase: Saturation
% 3.98/0.92  
% 3.98/0.92  % (24543)Memory used [KB]: 8571
% 3.98/0.92  % (24543)Time elapsed: 0.500 s
% 3.98/0.92  % (24543)------------------------------
% 3.98/0.92  % (24543)------------------------------
% 4.33/0.93  % (24532)Termination reason: Time limit
% 4.33/0.93  % (24532)Termination phase: Saturation
% 4.33/0.93  
% 4.33/0.93  % (24532)Memory used [KB]: 7547
% 4.33/0.93  % (24532)Time elapsed: 0.500 s
% 4.33/0.93  % (24532)------------------------------
% 4.33/0.93  % (24532)------------------------------
% 4.33/0.94  % (24531)Time limit reached!
% 4.33/0.94  % (24531)------------------------------
% 4.33/0.94  % (24531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.94  % (24531)Termination reason: Time limit
% 4.33/0.94  
% 4.33/0.94  % (24531)Memory used [KB]: 3709
% 4.33/0.94  % (24531)Time elapsed: 0.510 s
% 4.33/0.94  % (24531)------------------------------
% 4.33/0.94  % (24531)------------------------------
% 4.51/1.02  % (24559)Time limit reached!
% 4.51/1.02  % (24559)------------------------------
% 4.51/1.02  % (24559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/1.02  % (24559)Termination reason: Time limit
% 4.51/1.02  
% 4.51/1.02  % (24559)Memory used [KB]: 8571
% 4.51/1.02  % (24559)Time elapsed: 0.609 s
% 4.51/1.02  % (24559)------------------------------
% 4.51/1.02  % (24559)------------------------------
% 4.51/1.02  % (24593)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.00/1.05  % (24594)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.00/1.06  % (24547)Time limit reached!
% 5.00/1.06  % (24547)------------------------------
% 5.00/1.06  % (24547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.06  % (24547)Termination reason: Time limit
% 5.00/1.06  
% 5.00/1.06  % (24547)Memory used [KB]: 15095
% 5.00/1.06  % (24547)Time elapsed: 0.624 s
% 5.00/1.06  % (24547)------------------------------
% 5.00/1.06  % (24547)------------------------------
% 5.00/1.06  % (24595)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.00/1.06  % (24538)Time limit reached!
% 5.00/1.06  % (24538)------------------------------
% 5.00/1.06  % (24538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.06  % (24538)Termination reason: Time limit
% 5.00/1.06  
% 5.00/1.06  % (24538)Memory used [KB]: 9978
% 5.00/1.06  % (24538)Time elapsed: 0.617 s
% 5.00/1.06  % (24538)------------------------------
% 5.00/1.06  % (24538)------------------------------
% 5.69/1.11  % (24597)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.69/1.16  % (24596)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.30/1.17  % (24598)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.53/1.20  % (24602)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.53/1.21  % (24552)Time limit reached!
% 6.53/1.21  % (24552)------------------------------
% 6.53/1.21  % (24552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.53/1.21  % (24552)Termination reason: Time limit
% 6.53/1.21  % (24552)Termination phase: Saturation
% 6.53/1.21  
% 6.53/1.21  % (24552)Memory used [KB]: 5373
% 6.53/1.21  % (24552)Time elapsed: 0.800 s
% 6.53/1.21  % (24552)------------------------------
% 6.53/1.21  % (24552)------------------------------
% 6.83/1.24  % (24601)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 7.40/1.33  % (24606)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.40/1.35  % (24595)Time limit reached!
% 7.40/1.35  % (24595)------------------------------
% 7.40/1.35  % (24595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.40/1.35  % (24595)Termination reason: Time limit
% 7.40/1.35  
% 7.40/1.35  % (24595)Memory used [KB]: 13432
% 7.40/1.35  % (24595)Time elapsed: 0.405 s
% 7.40/1.35  % (24595)------------------------------
% 7.40/1.35  % (24595)------------------------------
% 7.92/1.38  % (24594)Time limit reached!
% 7.92/1.38  % (24594)------------------------------
% 7.92/1.38  % (24594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.92/1.38  % (24594)Termination reason: Time limit
% 7.92/1.38  
% 7.92/1.38  % (24594)Memory used [KB]: 6908
% 7.92/1.38  % (24594)Time elapsed: 0.439 s
% 7.92/1.38  % (24594)------------------------------
% 7.92/1.38  % (24594)------------------------------
% 7.92/1.42  % (24533)Time limit reached!
% 7.92/1.42  % (24533)------------------------------
% 7.92/1.42  % (24533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.92/1.42  % (24533)Termination reason: Time limit
% 7.92/1.42  
% 7.92/1.42  % (24533)Memory used [KB]: 19061
% 7.92/1.42  % (24533)Time elapsed: 1.015 s
% 7.92/1.42  % (24533)------------------------------
% 7.92/1.42  % (24533)------------------------------
% 8.79/1.49  % (24662)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.79/1.52  % (24684)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.09/1.56  % (24712)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.89/1.62  % (24557)Time limit reached!
% 9.89/1.62  % (24557)------------------------------
% 9.89/1.62  % (24557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.89/1.63  % (24557)Termination reason: Time limit
% 9.89/1.63  
% 9.89/1.63  % (24557)Memory used [KB]: 15607
% 9.89/1.63  % (24557)Time elapsed: 1.221 s
% 9.89/1.63  % (24557)------------------------------
% 9.89/1.63  % (24557)------------------------------
% 10.40/1.74  % (24546)Time limit reached!
% 10.40/1.74  % (24546)------------------------------
% 10.40/1.74  % (24546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.74  % (24546)Termination reason: Time limit
% 10.40/1.74  % (24546)Termination phase: Saturation
% 10.40/1.74  
% 10.40/1.74  % (24546)Memory used [KB]: 22643
% 10.40/1.74  % (24546)Time elapsed: 1.300 s
% 10.40/1.74  % (24546)------------------------------
% 10.40/1.74  % (24546)------------------------------
% 10.40/1.75  % (24555)Time limit reached!
% 10.40/1.75  % (24555)------------------------------
% 10.40/1.75  % (24555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.75  % (24555)Termination reason: Time limit
% 10.40/1.75  % (24555)Termination phase: Saturation
% 10.40/1.75  
% 10.40/1.75  % (24555)Memory used [KB]: 17526
% 10.40/1.75  % (24555)Time elapsed: 1.300 s
% 10.40/1.75  % (24555)------------------------------
% 10.40/1.75  % (24555)------------------------------
% 10.40/1.77  % (24780)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.47/1.87  % (24820)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.47/1.89  % (24829)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.08/1.90  % (24558)Time limit reached!
% 12.08/1.90  % (24558)------------------------------
% 12.08/1.90  % (24558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.90  % (24558)Termination reason: Time limit
% 12.08/1.90  % (24558)Termination phase: Saturation
% 12.08/1.90  
% 12.08/1.90  % (24558)Memory used [KB]: 15095
% 12.08/1.90  % (24558)Time elapsed: 1.500 s
% 12.08/1.90  % (24558)------------------------------
% 12.08/1.90  % (24558)------------------------------
% 12.08/1.91  % (24535)Time limit reached!
% 12.08/1.91  % (24535)------------------------------
% 12.08/1.91  % (24535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.91  % (24535)Termination reason: Time limit
% 12.08/1.91  % (24535)Termination phase: Saturation
% 12.08/1.91  
% 12.08/1.91  % (24535)Memory used [KB]: 17142
% 12.08/1.91  % (24535)Time elapsed: 1.500 s
% 12.08/1.91  % (24535)------------------------------
% 12.08/1.91  % (24535)------------------------------
% 12.08/1.93  % (24684)Time limit reached!
% 12.08/1.93  % (24684)------------------------------
% 12.08/1.93  % (24684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.93  % (24684)Termination reason: Time limit
% 12.08/1.93  
% 12.08/1.93  % (24684)Memory used [KB]: 3326
% 12.08/1.93  % (24684)Time elapsed: 0.523 s
% 12.08/1.93  % (24684)------------------------------
% 12.08/1.93  % (24684)------------------------------
% 12.60/2.00  % (24542)Time limit reached!
% 12.60/2.00  % (24542)------------------------------
% 12.60/2.00  % (24542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.60/2.00  % (24542)Termination reason: Time limit
% 12.60/2.00  % (24542)Termination phase: Saturation
% 12.60/2.00  
% 12.60/2.00  % (24542)Memory used [KB]: 15095
% 12.60/2.00  % (24542)Time elapsed: 1.600 s
% 12.60/2.00  % (24542)------------------------------
% 12.60/2.00  % (24542)------------------------------
% 12.60/2.04  % (24839)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.60/2.06  % (24841)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.21/2.07  % (24840)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.27/2.09  % (24549)Refutation found. Thanks to Tanya!
% 13.27/2.09  % SZS status Theorem for theBenchmark
% 13.27/2.09  % SZS output start Proof for theBenchmark
% 13.27/2.09  fof(f16523,plain,(
% 13.27/2.09    $false),
% 13.27/2.09    inference(avatar_sat_refutation,[],[f138,f143,f156,f172,f177,f196,f212,f213,f228,f233,f276,f285,f317,f332,f390,f396,f402,f408,f414,f416,f422,f424,f430,f438,f496,f498,f565,f616,f665,f670,f710,f808,f830,f1058,f1065,f1071,f1384,f1745,f1750,f1751,f2180,f2210,f2224,f2229,f2403,f2404,f2408,f2409,f2779,f3911,f3916,f3921,f3923,f3931,f3935,f3940,f3942,f3951,f3957,f3963,f3987,f3995,f4013,f4020,f4034,f4050,f4096,f4103,f4107,f4111,f4127,f4248,f4249,f4355,f4356,f4424,f4425,f4426,f4531,f4642,f5054,f5061,f5068,f5076,f5079,f5086,f5090,f5093,f5101,f5107,f5108,f5114,f5115,f5121,f5122,f5128,f5129,f5130,f5131,f5132,f5133,f5134,f5135,f5136,f5137,f5139,f5141,f5143,f5149,f5150,f5156,f5157,f5164,f5165,f5166,f5167,f5168,f5169,f5170,f5171,f5172,f5173,f5175,f5177,f5179,f5186,f5187,f5194,f5195,f5196,f5197,f5198,f5199,f5200,f5201,f5202,f5203,f5205,f5207,f5210,f5212,f5214,f5216,f5218,f5220,f5222,f5224,f5227,f5228,f5229,f5251,f5267,f5268,f5270,f5275,f5320,f5391,f5398,f5402,f5405,f5412,f5417,f5419,f5420,f5619,f5642,f5643,f5645,f5650,f5652,f5653,f5655,f5656,f5662,f5663,f5665,f5670,f5672,f5673,f5675,f5676,f5682,f5683,f5685,f5690,f5692,f5693,f5695,f5696,f5704,f5712,f5716,f5724,f5732,f5737,f5739,f5740,f5743,f5748,f5750,f5752,f5756,f5757,f5759,f5761,f5769,f5775,f5778,f5780,f5784,f5785,f5787,f5789,f5792,f5793,f5795,f5796,f5801,f5804,f5805,f5807,f5809,f5812,f5814,f5816,f5824,f5832,f5840,f5843,f5847,f5848,f5859,f5864,f5866,f5869,f5876,f6023,f6098,f6103,f6108,f6151,f6174,f9422,f9949,f9954,f10534,f10646,f10651,f10652,f10660,f10670,f10679,f10689,f10692,f10695,f10702,f10707,f10708,f10713,f10718,f10719,f10965,f10980,f10993,f10996,f12101,f13121,f14010,f14016,f14063,f14066,f14081,f14082,f14089,f14100,f14124,f14793,f14968,f14997,f14999,f15001,f15003,f15006,f15009,f15011,f15014,f15016,f15021,f15022,f15024,f15026,f15028,f15031,f15034,f15036,f15039,f15041,f15046,f15052,f16378,f16383,f16522])).
% 13.27/2.09  fof(f16522,plain,(
% 13.27/2.09    ~spl6_7 | ~spl6_47 | spl6_150 | ~spl6_20 | ~spl6_62),
% 13.27/2.09    inference(avatar_split_clause,[],[f16517,f4100,f419,f16519,f3928,f209])).
% 13.27/2.09  fof(f209,plain,(
% 13.27/2.09    spl6_7 <=> r1_tarski(sK1,sK0)),
% 13.27/2.09    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 13.27/2.09  fof(f3928,plain,(
% 13.27/2.09    spl6_47 <=> r1_tarski(sK1,sK1)),
% 13.27/2.09    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 13.27/2.10  fof(f16519,plain,(
% 13.27/2.10    spl6_150 <=> sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).
% 13.27/2.10  fof(f419,plain,(
% 13.27/2.10    spl6_20 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 13.27/2.10  fof(f4100,plain,(
% 13.27/2.10    spl6_62 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 13.27/2.10  fof(f16517,plain,(
% 13.27/2.10    sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK0) | (~spl6_20 | ~spl6_62)),
% 13.27/2.10    inference(forward_demodulation,[],[f16516,f6033])).
% 13.27/2.10  fof(f6033,plain,(
% 13.27/2.10    ( ! [X38] : (k4_xboole_0(X38,k1_xboole_0) = X38) )),
% 13.27/2.10    inference(forward_demodulation,[],[f6032,f64])).
% 13.27/2.10  fof(f64,plain,(
% 13.27/2.10    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 13.27/2.10    inference(cnf_transformation,[],[f11])).
% 13.27/2.10  fof(f11,axiom,(
% 13.27/2.10    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 13.27/2.10  fof(f6032,plain,(
% 13.27/2.10    ( ! [X38] : (k4_xboole_0(X38,k1_xboole_0) = k5_xboole_0(X38,k1_xboole_0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f5917,f499])).
% 13.27/2.10  fof(f499,plain,(
% 13.27/2.10    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f477,f64])).
% 13.27/2.10  fof(f477,plain,(
% 13.27/2.10    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 13.27/2.10    inference(superposition,[],[f112,f198])).
% 13.27/2.10  fof(f198,plain,(
% 13.27/2.10    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f62,f115])).
% 13.27/2.10  fof(f115,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f75,f69])).
% 13.27/2.10  fof(f69,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f9])).
% 13.27/2.10  fof(f9,axiom,(
% 13.27/2.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 13.27/2.10  fof(f75,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f31])).
% 13.27/2.10  fof(f31,plain,(
% 13.27/2.10    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 13.27/2.10    inference(ennf_transformation,[],[f7])).
% 13.27/2.10  fof(f7,axiom,(
% 13.27/2.10    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 13.27/2.10  fof(f62,plain,(
% 13.27/2.10    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f8])).
% 13.27/2.10  fof(f8,axiom,(
% 13.27/2.10    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 13.27/2.10  fof(f112,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 13.27/2.10    inference(definition_unfolding,[],[f70,f69])).
% 13.27/2.10  fof(f70,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f6])).
% 13.27/2.10  fof(f6,axiom,(
% 13.27/2.10    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 13.27/2.10  fof(f5917,plain,(
% 13.27/2.10    ( ! [X38] : (k4_xboole_0(X38,k1_xboole_0) = k5_xboole_0(X38,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 13.27/2.10    inference(superposition,[],[f238,f499])).
% 13.27/2.10  fof(f238,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 13.27/2.10    inference(superposition,[],[f112,f113])).
% 13.27/2.10  fof(f113,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 13.27/2.10    inference(definition_unfolding,[],[f65,f69,f69])).
% 13.27/2.10  fof(f65,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f1])).
% 13.27/2.10  fof(f1,axiom,(
% 13.27/2.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 13.27/2.10  fof(f16516,plain,(
% 13.27/2.10    k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK0) | (~spl6_20 | ~spl6_62)),
% 13.27/2.10    inference(forward_demodulation,[],[f16515,f7318])).
% 13.27/2.10  fof(f7318,plain,(
% 13.27/2.10    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f7196,f7264])).
% 13.27/2.10  fof(f7264,plain,(
% 13.27/2.10    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X1),X2)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f7263,f7258])).
% 13.27/2.10  fof(f7258,plain,(
% 13.27/2.10    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f7257,f499])).
% 13.27/2.10  fof(f7257,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f7230,f499])).
% 13.27/2.10  fof(f7230,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f541,f299])).
% 13.27/2.10  fof(f299,plain,(
% 13.27/2.10    ( ! [X14,X12,X13,X11] : (r2_hidden(sK5(X11,X12,k5_xboole_0(X13,k4_xboole_0(X14,X13))),X14) | k4_xboole_0(X11,X12) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) | r2_hidden(sK5(X11,X12,k5_xboole_0(X13,k4_xboole_0(X14,X13))),X11) | r2_hidden(sK5(X11,X12,k5_xboole_0(X13,k4_xboole_0(X14,X13))),X13)) )),
% 13.27/2.10    inference(resolution,[],[f99,f150])).
% 13.27/2.10  fof(f150,plain,(
% 13.27/2.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | r2_hidden(X4,X1) | r2_hidden(X4,X0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f130,f114])).
% 13.27/2.10  fof(f114,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 13.27/2.10    inference(definition_unfolding,[],[f68,f111])).
% 13.27/2.10  fof(f111,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 13.27/2.10    inference(definition_unfolding,[],[f66,f110])).
% 13.27/2.10  fof(f110,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f67,f109])).
% 13.27/2.10  fof(f109,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f87,f108])).
% 13.27/2.10  fof(f108,plain,(
% 13.27/2.10    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f102,f107])).
% 13.27/2.10  fof(f107,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f103,f106])).
% 13.27/2.10  fof(f106,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f104,f105])).
% 13.27/2.10  fof(f105,plain,(
% 13.27/2.10    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f18])).
% 13.27/2.10  fof(f18,axiom,(
% 13.27/2.10    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 13.27/2.10  fof(f104,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f17])).
% 13.27/2.10  fof(f17,axiom,(
% 13.27/2.10    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 13.27/2.10  fof(f103,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f16])).
% 13.27/2.10  fof(f16,axiom,(
% 13.27/2.10    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 13.27/2.10  fof(f102,plain,(
% 13.27/2.10    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f15])).
% 13.27/2.10  fof(f15,axiom,(
% 13.27/2.10    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 13.27/2.10  fof(f87,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f14])).
% 13.27/2.10  fof(f14,axiom,(
% 13.27/2.10    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 13.27/2.10  fof(f67,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f13])).
% 13.27/2.10  fof(f13,axiom,(
% 13.27/2.10    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 13.27/2.10  fof(f66,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f20])).
% 13.27/2.10  fof(f20,axiom,(
% 13.27/2.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 13.27/2.10  fof(f68,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f12])).
% 13.27/2.10  fof(f12,axiom,(
% 13.27/2.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 13.27/2.10  fof(f130,plain,(
% 13.27/2.10    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 13.27/2.10    inference(equality_resolution,[],[f123])).
% 13.27/2.10  fof(f123,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 13.27/2.10    inference(definition_unfolding,[],[f90,f111])).
% 13.27/2.10  fof(f90,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 13.27/2.10    inference(cnf_transformation,[],[f53])).
% 13.27/2.10  fof(f53,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 13.27/2.10  fof(f52,plain,(
% 13.27/2.10    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 13.27/2.10    introduced(choice_axiom,[])).
% 13.27/2.10  fof(f51,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(rectify,[],[f50])).
% 13.27/2.10  fof(f50,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(flattening,[],[f49])).
% 13.27/2.10  fof(f49,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(nnf_transformation,[],[f2])).
% 13.27/2.10  fof(f2,axiom,(
% 13.27/2.10    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 13.27/2.10  fof(f99,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 13.27/2.10    inference(cnf_transformation,[],[f58])).
% 13.27/2.10  fof(f58,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).
% 13.27/2.10  fof(f57,plain,(
% 13.27/2.10    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 13.27/2.10    introduced(choice_axiom,[])).
% 13.27/2.10  fof(f56,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(rectify,[],[f55])).
% 13.27/2.10  fof(f55,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(flattening,[],[f54])).
% 13.27/2.10  fof(f54,plain,(
% 13.27/2.10    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.27/2.10    inference(nnf_transformation,[],[f3])).
% 13.27/2.10  fof(f3,axiom,(
% 13.27/2.10    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 13.27/2.10  fof(f541,plain,(
% 13.27/2.10    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f124,f203])).
% 13.27/2.10  fof(f203,plain,(
% 13.27/2.10    ( ! [X4,X5,X3] : (~r2_hidden(X5,k4_xboole_0(X3,X4)) | ~r1_tarski(X3,X4)) )),
% 13.27/2.10    inference(global_subsumption,[],[f133,f202])).
% 13.27/2.10  fof(f202,plain,(
% 13.27/2.10    ( ! [X4,X5,X3] : (~r2_hidden(X5,X3) | ~r2_hidden(X5,k4_xboole_0(X3,X4)) | ~r1_tarski(X3,X4)) )),
% 13.27/2.10    inference(superposition,[],[f132,f115])).
% 13.27/2.10  fof(f132,plain,(
% 13.27/2.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 13.27/2.10    inference(equality_resolution,[],[f97])).
% 13.27/2.10  fof(f97,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 13.27/2.10    inference(cnf_transformation,[],[f58])).
% 13.27/2.10  fof(f133,plain,(
% 13.27/2.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 13.27/2.10    inference(equality_resolution,[],[f96])).
% 13.27/2.10  fof(f96,plain,(
% 13.27/2.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 13.27/2.10    inference(cnf_transformation,[],[f58])).
% 13.27/2.10  fof(f124,plain,(
% 13.27/2.10    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 13.27/2.10    inference(equality_resolution,[],[f81])).
% 13.27/2.10  fof(f81,plain,(
% 13.27/2.10    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 13.27/2.10    inference(cnf_transformation,[],[f44])).
% 13.27/2.10  fof(f44,plain,(
% 13.27/2.10    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.27/2.10    inference(flattening,[],[f43])).
% 13.27/2.10  fof(f43,plain,(
% 13.27/2.10    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.27/2.10    inference(nnf_transformation,[],[f5])).
% 13.27/2.10  fof(f5,axiom,(
% 13.27/2.10    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 13.27/2.10  fof(f507,plain,(
% 13.27/2.10    ( ! [X17] : (~r2_hidden(X17,k1_xboole_0)) )),
% 13.27/2.10    inference(duplicate_literal_removal,[],[f506])).
% 13.27/2.10  fof(f506,plain,(
% 13.27/2.10    ( ! [X17] : (~r2_hidden(X17,k1_xboole_0) | ~r2_hidden(X17,k1_xboole_0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f483,f499])).
% 13.27/2.10  fof(f483,plain,(
% 13.27/2.10    ( ! [X17,X16] : (~r2_hidden(X17,k1_xboole_0) | ~r2_hidden(X17,k4_xboole_0(k1_xboole_0,X16))) )),
% 13.27/2.10    inference(superposition,[],[f132,f198])).
% 13.27/2.10  fof(f7263,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f7227,f499])).
% 13.27/2.10  fof(f7227,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f541,f541,f299])).
% 13.27/2.10  fof(f7196,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X1,X1),X2)) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f541,f541,f99])).
% 13.27/2.10  fof(f16515,plain,(
% 13.27/2.10    k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) | ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK0) | (~spl6_20 | ~spl6_62)),
% 13.27/2.10    inference(forward_demodulation,[],[f16360,f4102])).
% 13.27/2.10  fof(f4102,plain,(
% 13.27/2.10    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) | ~spl6_62),
% 13.27/2.10    inference(avatar_component_clause,[],[f4100])).
% 13.27/2.10  fof(f16360,plain,(
% 13.27/2.10    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK0) | ~spl6_20),
% 13.27/2.10    inference(superposition,[],[f421,f1241])).
% 13.27/2.10  fof(f1241,plain,(
% 13.27/2.10    ( ! [X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X22,X23)) = X21 | ~r1_tarski(X21,X23) | ~r1_tarski(X21,X22)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f1240,f199])).
% 13.27/2.10  fof(f199,plain,(
% 13.27/2.10    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f124,f115])).
% 13.27/2.10  fof(f1240,plain,(
% 13.27/2.10    ( ! [X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X22,X23)) = k4_xboole_0(X21,k4_xboole_0(X21,X21)) | ~r1_tarski(X21,X23) | ~r1_tarski(X21,X22)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f1239,f1116])).
% 13.27/2.10  fof(f1116,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f124,f374])).
% 13.27/2.10  fof(f374,plain,(
% 13.27/2.10    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X8,X7)) = k5_xboole_0(k4_xboole_0(X6,X8),k4_xboole_0(X6,k4_xboole_0(X6,X8))) | ~r1_tarski(X6,X7)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f369,f114])).
% 13.27/2.10  fof(f369,plain,(
% 13.27/2.10    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X8,X7)) = k3_tarski(k6_enumset1(k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),X6)) | ~r1_tarski(X6,X7)) )),
% 13.27/2.10    inference(superposition,[],[f116,f115])).
% 13.27/2.10  fof(f116,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) )),
% 13.27/2.10    inference(definition_unfolding,[],[f88,f111,f69])).
% 13.27/2.10  fof(f88,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f10])).
% 13.27/2.10  fof(f10,axiom,(
% 13.27/2.10    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 13.27/2.10  fof(f1239,plain,(
% 13.27/2.10    ( ! [X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X22,X23)) = k5_xboole_0(k4_xboole_0(X21,X21),k4_xboole_0(X21,k4_xboole_0(X21,X21))) | ~r1_tarski(X21,X23) | ~r1_tarski(X21,X22)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f1139,f525])).
% 13.27/2.10  fof(f525,plain,(
% 13.27/2.10    ( ! [X4] : (k4_xboole_0(X4,X4) = k5_xboole_0(X4,X4)) )),
% 13.27/2.10    inference(superposition,[],[f112,f199])).
% 13.27/2.10  fof(f1139,plain,(
% 13.27/2.10    ( ! [X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X22,X23)) = k5_xboole_0(k5_xboole_0(X21,X21),k4_xboole_0(X21,k5_xboole_0(X21,X21))) | ~r1_tarski(X21,X23) | ~r1_tarski(X21,X22)) )),
% 13.27/2.10    inference(superposition,[],[f374,f235])).
% 13.27/2.10  fof(f235,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 13.27/2.10    inference(superposition,[],[f112,f115])).
% 13.27/2.10  fof(f421,plain,(
% 13.27/2.10    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl6_20),
% 13.27/2.10    inference(avatar_component_clause,[],[f419])).
% 13.27/2.10  fof(f16383,plain,(
% 13.27/2.10    spl6_149 | ~spl6_7),
% 13.27/2.10    inference(avatar_split_clause,[],[f16157,f209,f16380])).
% 13.27/2.10  fof(f16380,plain,(
% 13.27/2.10    spl6_149 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_149])])).
% 13.27/2.10  fof(f16157,plain,(
% 13.27/2.10    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl6_7),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f211,f124,f1241])).
% 13.27/2.10  fof(f211,plain,(
% 13.27/2.10    r1_tarski(sK1,sK0) | ~spl6_7),
% 13.27/2.10    inference(avatar_component_clause,[],[f209])).
% 13.27/2.10  fof(f16378,plain,(
% 13.27/2.10    spl6_148 | ~spl6_28 | ~spl6_36),
% 13.27/2.10    inference(avatar_split_clause,[],[f16373,f1747,f707,f16375])).
% 13.27/2.10  fof(f16375,plain,(
% 13.27/2.10    spl6_148 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).
% 13.27/2.10  fof(f707,plain,(
% 13.27/2.10    spl6_28 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 13.27/2.10  fof(f1747,plain,(
% 13.27/2.10    spl6_36 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 13.27/2.10  fof(f16373,plain,(
% 13.27/2.10    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | (~spl6_28 | ~spl6_36)),
% 13.27/2.10    inference(forward_demodulation,[],[f16158,f709])).
% 13.27/2.10  fof(f709,plain,(
% 13.27/2.10    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_28),
% 13.27/2.10    inference(avatar_component_clause,[],[f707])).
% 13.27/2.10  fof(f16158,plain,(
% 13.27/2.10    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_36),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f1749,f124,f1241])).
% 13.27/2.10  fof(f1749,plain,(
% 13.27/2.10    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl6_36),
% 13.27/2.10    inference(avatar_component_clause,[],[f1747])).
% 13.27/2.10  fof(f15052,plain,(
% 13.27/2.10    ~spl6_147 | spl6_50 | ~spl6_71),
% 13.27/2.10    inference(avatar_split_clause,[],[f15047,f5058,f3944,f15049])).
% 13.27/2.10  fof(f15049,plain,(
% 13.27/2.10    spl6_147 <=> r1_tarski(k1_xboole_0,sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).
% 13.27/2.10  fof(f3944,plain,(
% 13.27/2.10    spl6_50 <=> r1_tarski(k4_xboole_0(sK1,sK0),sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 13.27/2.10  fof(f5058,plain,(
% 13.27/2.10    spl6_71 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 13.27/2.10  fof(f15047,plain,(
% 13.27/2.10    ~r1_tarski(k1_xboole_0,sK1) | (spl6_50 | ~spl6_71)),
% 13.27/2.10    inference(forward_demodulation,[],[f3946,f5060])).
% 13.27/2.10  fof(f5060,plain,(
% 13.27/2.10    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_71),
% 13.27/2.10    inference(avatar_component_clause,[],[f5058])).
% 13.27/2.10  fof(f3946,plain,(
% 13.27/2.10    ~r1_tarski(k4_xboole_0(sK1,sK0),sK1) | spl6_50),
% 13.27/2.10    inference(avatar_component_clause,[],[f3944])).
% 13.27/2.10  fof(f15046,plain,(
% 13.27/2.10    spl6_146 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f14971,f14097,f15043])).
% 13.27/2.10  fof(f15043,plain,(
% 13.27/2.10    spl6_146 <=> r2_hidden(sK2(k1_xboole_0,sK1),sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_146])])).
% 13.27/2.10  fof(f14097,plain,(
% 13.27/2.10    spl6_139 <=> k1_xboole_0 = sK1),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).
% 13.27/2.10  fof(f14971,plain,(
% 13.27/2.10    r2_hidden(sK2(k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f14098,f78])).
% 13.27/2.10  fof(f78,plain,(
% 13.27/2.10    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f42])).
% 13.27/2.10  fof(f42,plain,(
% 13.27/2.10    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 13.27/2.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 13.27/2.10  fof(f41,plain,(
% 13.27/2.10    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 13.27/2.10    introduced(choice_axiom,[])).
% 13.27/2.10  fof(f40,plain,(
% 13.27/2.10    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 13.27/2.10    inference(nnf_transformation,[],[f34])).
% 13.27/2.10  fof(f34,plain,(
% 13.27/2.10    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 13.27/2.10    inference(ennf_transformation,[],[f4])).
% 13.27/2.10  fof(f4,axiom,(
% 13.27/2.10    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 13.27/2.10  fof(f14098,plain,(
% 13.27/2.10    k1_xboole_0 != sK1 | spl6_139),
% 13.27/2.10    inference(avatar_component_clause,[],[f14097])).
% 13.27/2.10  fof(f15041,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15040,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f14994,plain,(
% 13.27/2.10    spl6_144 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).
% 13.27/2.10  fof(f15040,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14973,f5060])).
% 13.27/2.10  fof(f14973,plain,(
% 13.27/2.10    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f542,f542,f542,f542,f14098,f351])).
% 13.27/2.10  fof(f351,plain,(
% 13.27/2.10    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X3) | r2_hidden(sK4(X0,X1,X3),X1) | r2_hidden(sK4(X0,X1,X3),X0) | X2 = X3 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.27/2.10    inference(superposition,[],[f147,f147])).
% 13.27/2.10  fof(f147,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.27/2.10    inference(forward_demodulation,[],[f120,f114])).
% 13.27/2.10  fof(f120,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.27/2.10    inference(definition_unfolding,[],[f93,f111])).
% 13.27/2.10  fof(f93,plain,(
% 13.27/2.10    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.27/2.10    inference(cnf_transformation,[],[f53])).
% 13.27/2.10  fof(f542,plain,(
% 13.27/2.10    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,sK0))) ) | ~spl6_7),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f211,f203])).
% 13.27/2.10  fof(f15039,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15038,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15038,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f15037,f7318])).
% 13.27/2.10  fof(f15037,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)) ) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14974,f5060])).
% 13.27/2.10  fof(f14974,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(sK1,sK0),sK1),sK1)) ) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f541,f541,f542,f542,f14098,f351])).
% 13.27/2.10  fof(f15036,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15035,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15035,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14975,f5060])).
% 13.27/2.10  fof(f14975,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f507,f542,f542,f14098,f351])).
% 13.27/2.10  fof(f15034,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15033,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15033,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f15032,f5060])).
% 13.27/2.10  fof(f15032,plain,(
% 13.27/2.10    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14976,f7318])).
% 13.27/2.10  fof(f14976,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,X0),sK1),sK1)) ) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f542,f542,f541,f541,f14098,f351])).
% 13.27/2.10  fof(f15031,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15030,f14097,f14994])).
% 13.27/2.10  fof(f15030,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f15029,f7318])).
% 13.27/2.10  fof(f15029,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f14977,f7318])).
% 13.27/2.10  fof(f14977,plain,(
% 13.27/2.10    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1),sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f541,f541,f541,f541,f14098,f351])).
% 13.27/2.10  fof(f15028,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15027,f14097,f14994])).
% 13.27/2.10  fof(f15027,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f14978,f7318])).
% 13.27/2.10  fof(f14978,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,k4_xboole_0(X0,X0),sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f507,f541,f541,f14098,f351])).
% 13.27/2.10  fof(f15026,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15025,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15025,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14979,f5060])).
% 13.27/2.10  fof(f14979,plain,(
% 13.27/2.10    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f507,f14098,f351])).
% 13.27/2.10  fof(f15024,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15023,f14097,f14994])).
% 13.27/2.10  fof(f15023,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f14980,f7318])).
% 13.27/2.10  fof(f14980,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f541,f541,f507,f14098,f351])).
% 13.27/2.10  fof(f15022,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f14981,f14097,f14994])).
% 13.27/2.10  fof(f14981,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f507,f507,f507,f14098,f351])).
% 13.27/2.10  fof(f15021,plain,(
% 13.27/2.10    spl6_145 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f14982,f14097,f15018])).
% 13.27/2.10  fof(f15018,plain,(
% 13.27/2.10    spl6_145 <=> r2_hidden(sK2(sK1,k1_xboole_0),sK1)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).
% 13.27/2.10  fof(f14982,plain,(
% 13.27/2.10    r2_hidden(sK2(sK1,k1_xboole_0),sK1) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f14098,f78])).
% 13.27/2.10  fof(f15016,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15015,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15015,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14984,f5060])).
% 13.27/2.10  fof(f14984,plain,(
% 13.27/2.10    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f542,f542,f507,f542,f542,f14098,f351])).
% 13.27/2.10  fof(f15014,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15013,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15013,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f15012,f7318])).
% 13.27/2.10  fof(f15012,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)) ) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14985,f5060])).
% 13.27/2.10  fof(f14985,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(sK1,sK0),sK1),sK1)) ) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f541,f541,f507,f542,f542,f14098,f351])).
% 13.27/2.10  fof(f15011,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15010,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15010,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14986,f5060])).
% 13.27/2.10  fof(f14986,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f507,f542,f542,f14098,f351])).
% 13.27/2.10  fof(f15009,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15008,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15008,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f15007,f5060])).
% 13.27/2.10  fof(f15007,plain,(
% 13.27/2.10    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14987,f7318])).
% 13.27/2.10  fof(f14987,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,X0),sK1),sK1)) ) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f542,f542,f507,f541,f541,f14098,f351])).
% 13.27/2.10  fof(f15006,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15005,f14097,f14994])).
% 13.27/2.10  fof(f15005,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f15004,f7318])).
% 13.27/2.10  fof(f15004,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f14988,f7318])).
% 13.27/2.10  fof(f14988,plain,(
% 13.27/2.10    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1),sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f541,f541,f507,f541,f541,f14098,f351])).
% 13.27/2.10  fof(f15003,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15002,f14097,f14994])).
% 13.27/2.10  fof(f15002,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f14989,f7318])).
% 13.27/2.10  fof(f14989,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,k4_xboole_0(X0,X0),sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f507,f541,f541,f14098,f351])).
% 13.27/2.10  fof(f15001,plain,(
% 13.27/2.10    spl6_144 | ~spl6_7 | ~spl6_71 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f15000,f14097,f5058,f209,f14994])).
% 13.27/2.10  fof(f15000,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | (~spl6_7 | ~spl6_71 | spl6_139)),
% 13.27/2.10    inference(forward_demodulation,[],[f14990,f5060])).
% 13.27/2.10  fof(f14990,plain,(
% 13.27/2.10    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,sK1),sK1) | (~spl6_7 | spl6_139)),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f507,f14098,f351])).
% 13.27/2.10  fof(f14999,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f14998,f14097,f14994])).
% 13.27/2.10  fof(f14998,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(forward_demodulation,[],[f14991,f7318])).
% 13.27/2.10  fof(f14991,plain,(
% 13.27/2.10    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(X0,X0),k1_xboole_0,sK1),sK1)) ) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f541,f541,f507,f14098,f351])).
% 13.27/2.10  fof(f14997,plain,(
% 13.27/2.10    spl6_144 | spl6_139),
% 13.27/2.10    inference(avatar_split_clause,[],[f14992,f14097,f14994])).
% 13.27/2.10  fof(f14992,plain,(
% 13.27/2.10    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK1),sK1) | spl6_139),
% 13.27/2.10    inference(unit_resulting_resolution,[],[f507,f507,f507,f507,f507,f14098,f351])).
% 13.27/2.10  fof(f14968,plain,(
% 13.27/2.10    spl6_142 | ~spl6_143),
% 13.27/2.10    inference(avatar_split_clause,[],[f14947,f14965,f14962])).
% 13.27/2.10  fof(f14962,plain,(
% 13.27/2.10    spl6_142 <=> ! [X40] : (m1_subset_1(X40,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(X40,k1_xboole_0))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).
% 13.27/2.10  fof(f14965,plain,(
% 13.27/2.10    spl6_143 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_143])])).
% 13.27/2.10  fof(f14947,plain,(
% 13.27/2.10    ( ! [X40] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(X40,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(X40,k1_xboole_0)) )),
% 13.27/2.10    inference(superposition,[],[f704,f499])).
% 13.27/2.10  fof(f704,plain,(
% 13.27/2.10    ( ! [X59,X60] : (~m1_subset_1(k4_xboole_0(X59,X60),k1_zfmisc_1(X59)) | m1_subset_1(X60,k1_zfmisc_1(X59)) | ~r1_tarski(X60,X59)) )),
% 13.27/2.10    inference(superposition,[],[f223,f236])).
% 13.27/2.10  fof(f236,plain,(
% 13.27/2.10    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 13.27/2.10    inference(superposition,[],[f113,f115])).
% 13.27/2.10  fof(f223,plain,(
% 13.27/2.10    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.10    inference(duplicate_literal_removal,[],[f222])).
% 13.27/2.10  fof(f222,plain,(
% 13.27/2.10    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.10    inference(superposition,[],[f76,f77])).
% 13.27/2.10  fof(f77,plain,(
% 13.27/2.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f33])).
% 13.27/2.10  fof(f33,plain,(
% 13.27/2.10    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.27/2.10    inference(ennf_transformation,[],[f23])).
% 13.27/2.10  fof(f23,axiom,(
% 13.27/2.10    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 13.27/2.10  fof(f76,plain,(
% 13.27/2.10    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.10    inference(cnf_transformation,[],[f32])).
% 13.27/2.10  fof(f32,plain,(
% 13.27/2.10    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.27/2.10    inference(ennf_transformation,[],[f24])).
% 13.27/2.10  fof(f24,axiom,(
% 13.27/2.10    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 13.27/2.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 13.27/2.10  fof(f14793,plain,(
% 13.27/2.10    spl6_140 | ~spl6_141),
% 13.27/2.10    inference(avatar_split_clause,[],[f14785,f14790,f14787])).
% 13.27/2.10  fof(f14787,plain,(
% 13.27/2.10    spl6_140 <=> ! [X29,X28,X30] : (~r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29)))) | ~r1_tarski(X28,X29))),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).
% 13.27/2.10  fof(f14790,plain,(
% 13.27/2.10    spl6_141 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 13.27/2.10    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).
% 13.27/2.11  fof(f14785,plain,(
% 13.27/2.11    ( ! [X30,X28,X29] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29)))) | ~r1_tarski(X28,X29)) )),
% 13.27/2.11    inference(global_subsumption,[],[f507,f14784])).
% 13.27/2.11  fof(f14784,plain,(
% 13.27/2.11    ( ! [X30,X28,X29] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | r2_hidden(X30,k1_xboole_0) | ~r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29)))) | ~r1_tarski(X28,X29)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f14783,f7318])).
% 13.27/2.11  fof(f14783,plain,(
% 13.27/2.11    ( ! [X30,X28,X29] : (r2_hidden(X30,k1_xboole_0) | ~r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29)))) | ~r1_tarski(k4_xboole_0(X28,X28),k4_xboole_0(X28,X28)) | ~r1_tarski(X28,X29)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f14584,f7318])).
% 13.27/2.11  fof(f14584,plain,(
% 13.27/2.11    ( ! [X30,X28,X29] : (~r2_hidden(X30,k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X28,X29)))) | r2_hidden(X30,k4_xboole_0(X28,X28)) | ~r1_tarski(k4_xboole_0(X28,X28),k4_xboole_0(X28,X28)) | ~r1_tarski(X28,X29)) )),
% 13.27/2.11    inference(superposition,[],[f643,f373])).
% 13.27/2.11  fof(f373,plain,(
% 13.27/2.11    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7))) = k5_xboole_0(k4_xboole_0(X6,X8),k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X8))) | ~r1_tarski(X6,X7)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f366,f114])).
% 13.27/2.11  fof(f366,plain,(
% 13.27/2.11    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X6,X7))) = k3_tarski(k6_enumset1(k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X8),k4_xboole_0(X6,X6))) | ~r1_tarski(X6,X7)) )),
% 13.27/2.11    inference(superposition,[],[f116,f115])).
% 13.27/2.11  fof(f643,plain,(
% 13.27/2.11    ( ! [X43,X41,X42] : (~r2_hidden(X43,k5_xboole_0(X42,k4_xboole_0(X41,X41))) | r2_hidden(X43,X42) | ~r1_tarski(X41,X42)) )),
% 13.27/2.11    inference(global_subsumption,[],[f543,f642])).
% 13.27/2.11  fof(f642,plain,(
% 13.27/2.11    ( ! [X43,X41,X42] : (~r2_hidden(X43,k5_xboole_0(X42,k4_xboole_0(X41,X41))) | r2_hidden(X43,X41) | r2_hidden(X43,X42) | ~r1_tarski(X41,X42)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f600,f525])).
% 13.27/2.11  fof(f600,plain,(
% 13.27/2.11    ( ! [X43,X41,X42] : (~r2_hidden(X43,k5_xboole_0(X42,k5_xboole_0(X41,X41))) | r2_hidden(X43,X41) | r2_hidden(X43,X42) | ~r1_tarski(X41,X42)) )),
% 13.27/2.11    inference(superposition,[],[f150,f235])).
% 13.27/2.11  fof(f543,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 13.27/2.11    inference(resolution,[],[f203,f131])).
% 13.27/2.11  fof(f131,plain,(
% 13.27/2.11    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 13.27/2.11    inference(equality_resolution,[],[f98])).
% 13.27/2.11  fof(f98,plain,(
% 13.27/2.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 13.27/2.11    inference(cnf_transformation,[],[f58])).
% 13.27/2.11  fof(f14124,plain,(
% 13.27/2.11    ~spl6_115 | spl6_126),
% 13.27/2.11    inference(avatar_split_clause,[],[f11805,f10715,f9419])).
% 13.27/2.11  fof(f9419,plain,(
% 13.27/2.11    spl6_115 <=> r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).
% 13.27/2.11  fof(f10715,plain,(
% 13.27/2.11    spl6_126 <=> r1_tarski(sK1,k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).
% 13.27/2.11  fof(f11805,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | spl6_126),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f10717,f127])).
% 13.27/2.11  fof(f127,plain,(
% 13.27/2.11    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 13.27/2.11    inference(equality_resolution,[],[f83])).
% 13.27/2.11  fof(f83,plain,(
% 13.27/2.11    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 13.27/2.11    inference(cnf_transformation,[],[f48])).
% 13.27/2.11  fof(f48,plain,(
% 13.27/2.11    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 13.27/2.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 13.27/2.11  fof(f47,plain,(
% 13.27/2.11    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 13.27/2.11    introduced(choice_axiom,[])).
% 13.27/2.11  fof(f46,plain,(
% 13.27/2.11    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 13.27/2.11    inference(rectify,[],[f45])).
% 13.27/2.11  fof(f45,plain,(
% 13.27/2.11    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 13.27/2.11    inference(nnf_transformation,[],[f19])).
% 13.27/2.11  fof(f19,axiom,(
% 13.27/2.11    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 13.27/2.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 13.27/2.11  fof(f10717,plain,(
% 13.27/2.11    ~r1_tarski(sK1,k1_xboole_0) | spl6_126),
% 13.27/2.11    inference(avatar_component_clause,[],[f10715])).
% 13.27/2.11  fof(f14100,plain,(
% 13.27/2.11    spl6_139 | ~spl6_44),
% 13.27/2.11    inference(avatar_split_clause,[],[f14095,f3908,f14097])).
% 13.27/2.11  fof(f3908,plain,(
% 13.27/2.11    spl6_44 <=> sK1 = k4_xboole_0(sK1,sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 13.27/2.11  fof(f14095,plain,(
% 13.27/2.11    k1_xboole_0 = sK1 | ~spl6_44),
% 13.27/2.11    inference(forward_demodulation,[],[f3910,f7318])).
% 13.27/2.11  fof(f3910,plain,(
% 13.27/2.11    sK1 = k4_xboole_0(sK1,sK1) | ~spl6_44),
% 13.27/2.11    inference(avatar_component_clause,[],[f3908])).
% 13.27/2.11  fof(f14089,plain,(
% 13.27/2.11    spl6_138 | ~spl6_68),
% 13.27/2.11    inference(avatar_split_clause,[],[f14084,f4528,f14086])).
% 13.27/2.11  fof(f14086,plain,(
% 13.27/2.11    spl6_138 <=> sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).
% 13.27/2.11  fof(f4528,plain,(
% 13.27/2.11    spl6_68 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 13.27/2.11  fof(f14084,plain,(
% 13.27/2.11    sK0 = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_68),
% 13.27/2.11    inference(forward_demodulation,[],[f14083,f6033])).
% 13.27/2.11  fof(f14083,plain,(
% 13.27/2.11    k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_68),
% 13.27/2.11    inference(forward_demodulation,[],[f4530,f7318])).
% 13.27/2.11  fof(f4530,plain,(
% 13.27/2.11    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1)) | ~spl6_68),
% 13.27/2.11    inference(avatar_component_clause,[],[f4528])).
% 13.27/2.11  fof(f14082,plain,(
% 13.27/2.11    ~spl6_115 | spl6_125),
% 13.27/2.11    inference(avatar_split_clause,[],[f13183,f10710,f9419])).
% 13.27/2.11  fof(f10710,plain,(
% 13.27/2.11    spl6_125 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).
% 13.27/2.11  fof(f13183,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | spl6_125),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f61,f10712,f72])).
% 13.27/2.11  fof(f72,plain,(
% 13.27/2.11    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 13.27/2.11    inference(cnf_transformation,[],[f39])).
% 13.27/2.11  fof(f39,plain,(
% 13.27/2.11    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 13.27/2.11    inference(nnf_transformation,[],[f30])).
% 13.27/2.11  fof(f30,plain,(
% 13.27/2.11    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 13.27/2.11    inference(ennf_transformation,[],[f21])).
% 13.27/2.11  fof(f21,axiom,(
% 13.27/2.11    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 13.27/2.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 13.27/2.11  fof(f10712,plain,(
% 13.27/2.11    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | spl6_125),
% 13.27/2.11    inference(avatar_component_clause,[],[f10710])).
% 13.27/2.11  fof(f61,plain,(
% 13.27/2.11    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(cnf_transformation,[],[f25])).
% 13.27/2.11  fof(f25,axiom,(
% 13.27/2.11    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 13.27/2.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 13.27/2.11  fof(f14081,plain,(
% 13.27/2.11    spl6_137 | ~spl6_115 | spl6_125),
% 13.27/2.11    inference(avatar_split_clause,[],[f13184,f10710,f9419,f14078])).
% 13.27/2.11  fof(f14078,plain,(
% 13.27/2.11    spl6_137 <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).
% 13.27/2.11  fof(f13184,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | spl6_125),
% 13.27/2.11    inference(resolution,[],[f10712,f72])).
% 13.27/2.11  fof(f14066,plain,(
% 13.27/2.11    ~spl6_7 | spl6_136 | spl6_43),
% 13.27/2.11    inference(avatar_split_clause,[],[f13887,f3904,f14014,f209])).
% 13.27/2.11  fof(f14014,plain,(
% 13.27/2.11    spl6_136 <=> ! [X594] : (~r1_tarski(sK1,k4_xboole_0(sK1,X594)) | ~r1_tarski(sK1,X594))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).
% 13.27/2.11  fof(f3904,plain,(
% 13.27/2.11    spl6_43 <=> r1_tarski(sK1,k4_xboole_0(sK1,sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 13.27/2.11  fof(f13887,plain,(
% 13.27/2.11    ( ! [X594] : (~r1_tarski(sK1,k4_xboole_0(sK1,X594)) | ~r1_tarski(sK1,sK0) | ~r1_tarski(sK1,X594)) ) | spl6_43),
% 13.27/2.11    inference(superposition,[],[f3906,f584])).
% 13.27/2.11  fof(f584,plain,(
% 13.27/2.11    ( ! [X2,X3,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,X3) | ~r1_tarski(X1,X3) | ~r1_tarski(X1,X2)) )),
% 13.27/2.11    inference(superposition,[],[f235,f235])).
% 13.27/2.11  fof(f3906,plain,(
% 13.27/2.11    ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | spl6_43),
% 13.27/2.11    inference(avatar_component_clause,[],[f3904])).
% 13.27/2.11  fof(f14063,plain,(
% 13.27/2.11    ~spl6_134 | spl6_135 | ~spl6_19),
% 13.27/2.11    inference(avatar_split_clause,[],[f13860,f411,f14008,f14004])).
% 13.27/2.11  fof(f14004,plain,(
% 13.27/2.11    spl6_134 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).
% 13.27/2.11  fof(f14008,plain,(
% 13.27/2.11    spl6_135 <=> ! [X556] : (k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),X556)) | ~r1_tarski(k4_xboole_0(sK0,sK1),X556))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).
% 13.27/2.11  fof(f411,plain,(
% 13.27/2.11    spl6_19 <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 13.27/2.11  fof(f13860,plain,(
% 13.27/2.11    ( ! [X556] : (k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),X556)) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~r1_tarski(k4_xboole_0(sK0,sK1),X556)) ) | ~spl6_19),
% 13.27/2.11    inference(superposition,[],[f413,f584])).
% 13.27/2.11  fof(f413,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | ~spl6_19),
% 13.27/2.11    inference(avatar_component_clause,[],[f411])).
% 13.27/2.11  fof(f14016,plain,(
% 13.27/2.11    ~spl6_7 | spl6_136 | spl6_43),
% 13.27/2.11    inference(avatar_split_clause,[],[f13703,f3904,f14014,f209])).
% 13.27/2.11  fof(f13703,plain,(
% 13.27/2.11    ( ! [X594] : (~r1_tarski(sK1,k4_xboole_0(sK1,X594)) | ~r1_tarski(sK1,X594) | ~r1_tarski(sK1,sK0)) ) | spl6_43),
% 13.27/2.11    inference(superposition,[],[f3906,f584])).
% 13.27/2.11  fof(f14010,plain,(
% 13.27/2.11    ~spl6_134 | spl6_135 | ~spl6_19),
% 13.27/2.11    inference(avatar_split_clause,[],[f13676,f411,f14008,f14004])).
% 13.27/2.11  fof(f13676,plain,(
% 13.27/2.11    ( ! [X556] : (k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),X556)) | ~r1_tarski(k4_xboole_0(sK0,sK1),X556) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK1)) ) | ~spl6_19),
% 13.27/2.11    inference(superposition,[],[f413,f584])).
% 13.27/2.11  fof(f13121,plain,(
% 13.27/2.11    spl6_132 | spl6_133 | ~spl6_4),
% 13.27/2.11    inference(avatar_split_clause,[],[f13113,f169,f13118,f13115])).
% 13.27/2.11  fof(f13115,plain,(
% 13.27/2.11    spl6_132 <=> ! [X264] : ~r1_tarski(k1_zfmisc_1(sK0),X264)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).
% 13.27/2.11  fof(f13118,plain,(
% 13.27/2.11    spl6_133 <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(sK0)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).
% 13.27/2.11  fof(f169,plain,(
% 13.27/2.11    spl6_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 13.27/2.11  fof(f13113,plain,(
% 13.27/2.11    ( ! [X264] : (r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(sK0))) | ~r1_tarski(k1_zfmisc_1(sK0),X264)) ) | ~spl6_4),
% 13.27/2.11    inference(forward_demodulation,[],[f12865,f7264])).
% 13.27/2.11  fof(f12865,plain,(
% 13.27/2.11    ( ! [X264] : (r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),X264),k1_zfmisc_1(sK0))) | ~r1_tarski(k1_zfmisc_1(sK0),X264)) ) | ~spl6_4),
% 13.27/2.11    inference(superposition,[],[f215,f1235])).
% 13.27/2.11  fof(f1235,plain,(
% 13.27/2.11    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(k4_xboole_0(X12,X12),X13)) = X12 | ~r1_tarski(X12,X13)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f1136,f526])).
% 13.27/2.11  fof(f526,plain,(
% 13.27/2.11    ( ! [X6] : (k5_xboole_0(X6,k4_xboole_0(X6,X6)) = X6) )),
% 13.27/2.11    inference(superposition,[],[f112,f199])).
% 13.27/2.11  fof(f1136,plain,(
% 13.27/2.11    ( ! [X12,X13] : (k5_xboole_0(X12,k4_xboole_0(X12,X12)) = k4_xboole_0(X12,k4_xboole_0(k4_xboole_0(X12,X12),X13)) | ~r1_tarski(X12,X13)) )),
% 13.27/2.11    inference(superposition,[],[f374,f199])).
% 13.27/2.11  fof(f215,plain,(
% 13.27/2.11    ( ! [X0] : (r2_hidden(sK1,k5_xboole_0(X0,k4_xboole_0(k1_zfmisc_1(sK0),X0)))) ) | ~spl6_4),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f171,f148])).
% 13.27/2.11  fof(f148,plain,(
% 13.27/2.11    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X1)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f128,f114])).
% 13.27/2.11  fof(f128,plain,(
% 13.27/2.11    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 13.27/2.11    inference(equality_resolution,[],[f121])).
% 13.27/2.11  fof(f121,plain,(
% 13.27/2.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 13.27/2.11    inference(definition_unfolding,[],[f92,f111])).
% 13.27/2.11  fof(f92,plain,(
% 13.27/2.11    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 13.27/2.11    inference(cnf_transformation,[],[f53])).
% 13.27/2.11  fof(f171,plain,(
% 13.27/2.11    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl6_4),
% 13.27/2.11    inference(avatar_component_clause,[],[f169])).
% 13.27/2.11  fof(f12101,plain,(
% 13.27/2.11    spl6_131 | ~spl6_36),
% 13.27/2.11    inference(avatar_split_clause,[],[f12096,f1747,f12098])).
% 13.27/2.11  fof(f12098,plain,(
% 13.27/2.11    spl6_131 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).
% 13.27/2.11  fof(f12096,plain,(
% 13.27/2.11    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl6_36),
% 13.27/2.11    inference(forward_demodulation,[],[f11809,f7318])).
% 13.27/2.11  fof(f11809,plain,(
% 13.27/2.11    k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl6_36),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f1749,f1247])).
% 13.27/2.11  fof(f1247,plain,(
% 13.27/2.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f1246,f112])).
% 13.27/2.11  fof(f1246,plain,(
% 13.27/2.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 13.27/2.11    inference(forward_demodulation,[],[f1153,f1116])).
% 13.27/2.11  fof(f1153,plain,(
% 13.27/2.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0)))) | ~r1_tarski(X0,X1)) )),
% 13.27/2.11    inference(superposition,[],[f112,f374])).
% 13.27/2.11  fof(f10996,plain,(
% 13.27/2.11    ~spl6_127 | spl6_128 | ~spl6_19),
% 13.27/2.11    inference(avatar_split_clause,[],[f10953,f411,f10962,f10958])).
% 13.27/2.11  fof(f10958,plain,(
% 13.27/2.11    spl6_127 <=> r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).
% 13.27/2.11  fof(f10962,plain,(
% 13.27/2.11    spl6_128 <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).
% 13.27/2.11  fof(f10953,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | ~r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK1) | ~spl6_19),
% 13.27/2.11    inference(superposition,[],[f413,f687])).
% 13.27/2.11  fof(f687,plain,(
% 13.27/2.11    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(X7,X8) | ~r1_tarski(X8,X7)) )),
% 13.27/2.11    inference(superposition,[],[f112,f236])).
% 13.27/2.11  fof(f10993,plain,(
% 13.27/2.11    ~spl6_129 | spl6_130 | ~spl6_20 | ~spl6_62),
% 13.27/2.11    inference(avatar_split_clause,[],[f10992,f4100,f419,f10977,f10973])).
% 13.27/2.11  fof(f10973,plain,(
% 13.27/2.11    spl6_129 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).
% 13.27/2.11  fof(f10977,plain,(
% 13.27/2.11    spl6_130 <=> sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).
% 13.27/2.11  fof(f10992,plain,(
% 13.27/2.11    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.27/2.11    inference(forward_demodulation,[],[f10991,f6033])).
% 13.27/2.11  fof(f10991,plain,(
% 13.27/2.11    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.27/2.11    inference(forward_demodulation,[],[f10990,f7318])).
% 13.27/2.11  fof(f10990,plain,(
% 13.27/2.11    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.27/2.11    inference(forward_demodulation,[],[f10947,f4102])).
% 13.27/2.11  fof(f10947,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_20),
% 13.27/2.11    inference(superposition,[],[f421,f687])).
% 13.27/2.11  fof(f10980,plain,(
% 13.27/2.11    ~spl6_129 | spl6_130 | ~spl6_20 | ~spl6_62),
% 13.27/2.11    inference(avatar_split_clause,[],[f10971,f4100,f419,f10977,f10973])).
% 13.27/2.11  fof(f10971,plain,(
% 13.27/2.11    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.27/2.11    inference(forward_demodulation,[],[f10970,f6033])).
% 13.27/2.11  fof(f10970,plain,(
% 13.27/2.11    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.27/2.11    inference(forward_demodulation,[],[f10969,f7318])).
% 13.27/2.11  fof(f10969,plain,(
% 13.27/2.11    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.27/2.11    inference(forward_demodulation,[],[f10905,f4102])).
% 13.27/2.11  fof(f10905,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_20),
% 13.27/2.11    inference(superposition,[],[f687,f421])).
% 13.27/2.11  fof(f10965,plain,(
% 13.27/2.11    ~spl6_127 | spl6_128 | ~spl6_19),
% 13.27/2.11    inference(avatar_split_clause,[],[f10897,f411,f10962,f10958])).
% 13.27/2.11  fof(f10897,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | ~r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK1) | ~spl6_19),
% 13.27/2.11    inference(superposition,[],[f687,f413])).
% 13.27/2.11  fof(f10719,plain,(
% 13.27/2.11    ~spl6_126 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10640,f9419,f10715])).
% 13.27/2.11  fof(f10640,plain,(
% 13.27/2.11    ~r1_tarski(sK1,k1_xboole_0) | spl6_115),
% 13.27/2.11    inference(resolution,[],[f9421,f126])).
% 13.27/2.11  fof(f126,plain,(
% 13.27/2.11    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 13.27/2.11    inference(equality_resolution,[],[f84])).
% 13.27/2.11  fof(f84,plain,(
% 13.27/2.11    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 13.27/2.11    inference(cnf_transformation,[],[f48])).
% 13.27/2.11  fof(f9421,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | spl6_115),
% 13.27/2.11    inference(avatar_component_clause,[],[f9419])).
% 13.27/2.11  fof(f10718,plain,(
% 13.27/2.11    ~spl6_126 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10593,f9419,f10715])).
% 13.27/2.11  fof(f10593,plain,(
% 13.27/2.11    ~r1_tarski(sK1,k1_xboole_0) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f9421,f126])).
% 13.27/2.11  fof(f10713,plain,(
% 13.27/2.11    ~spl6_125 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10594,f9419,f10710])).
% 13.27/2.11  fof(f10594,plain,(
% 13.27/2.11    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f61,f9421,f71])).
% 13.27/2.11  fof(f71,plain,(
% 13.27/2.11    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 13.27/2.11    inference(cnf_transformation,[],[f39])).
% 13.27/2.11  fof(f10708,plain,(
% 13.27/2.11    spl6_123 | ~spl6_4 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10595,f9419,f169,f10699])).
% 13.27/2.11  fof(f10699,plain,(
% 13.27/2.11    spl6_123 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).
% 13.27/2.11  fof(f10595,plain,(
% 13.27/2.11    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))) | (~spl6_4 | spl6_115)),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f171,f9421,f131])).
% 13.27/2.11  fof(f10707,plain,(
% 13.27/2.11    spl6_124 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10596,f9419,f10704])).
% 13.27/2.11  fof(f10704,plain,(
% 13.27/2.11    spl6_124 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).
% 13.27/2.11  fof(f10596,plain,(
% 13.27/2.11    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f161,f9421,f131])).
% 13.27/2.11  fof(f161,plain,(
% 13.27/2.11    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f124,f126])).
% 13.27/2.11  fof(f10702,plain,(
% 13.27/2.11    spl6_123 | ~spl6_29 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10697,f9419,f805,f10699])).
% 13.27/2.11  fof(f805,plain,(
% 13.27/2.11    spl6_29 <=> r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 13.27/2.11  fof(f10697,plain,(
% 13.27/2.11    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))) | (~spl6_29 | spl6_115)),
% 13.27/2.11    inference(forward_demodulation,[],[f10600,f1231])).
% 13.27/2.11  fof(f1231,plain,(
% 13.27/2.11    ( ! [X8] : (k5_xboole_0(k4_xboole_0(X8,X8),X8) = X8) )),
% 13.27/2.11    inference(global_subsumption,[],[f124,f1130])).
% 13.27/2.11  fof(f1130,plain,(
% 13.27/2.11    ( ! [X8] : (k5_xboole_0(k4_xboole_0(X8,X8),X8) = X8 | ~r1_tarski(X8,X8)) )),
% 13.27/2.11    inference(superposition,[],[f374,f199])).
% 13.27/2.11  fof(f10600,plain,(
% 13.27/2.11    r2_hidden(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_xboole_0))) | (~spl6_29 | spl6_115)),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f807,f9421,f131])).
% 13.27/2.11  fof(f807,plain,(
% 13.27/2.11    r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.27/2.11    inference(avatar_component_clause,[],[f805])).
% 13.27/2.11  fof(f10695,plain,(
% 13.27/2.11    ~spl6_120 | ~spl6_7 | ~spl6_71 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10694,f9419,f5058,f209,f10657])).
% 13.27/2.11  fof(f10657,plain,(
% 13.27/2.11    spl6_120 <=> r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).
% 13.27/2.11  fof(f10694,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) | (~spl6_7 | ~spl6_71 | spl6_115)),
% 13.27/2.11    inference(forward_demodulation,[],[f10693,f6033])).
% 13.27/2.11  fof(f10693,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))) | (~spl6_7 | ~spl6_71 | spl6_115)),
% 13.27/2.11    inference(forward_demodulation,[],[f10607,f5060])).
% 13.27/2.11  fof(f10607,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(sK1,sK0)))) | (~spl6_7 | spl6_115)),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f542,f9421,f150])).
% 13.27/2.11  fof(f10692,plain,(
% 13.27/2.11    ~spl6_120 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10691,f9419,f10657])).
% 13.27/2.11  fof(f10691,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10690,f6033])).
% 13.27/2.11  fof(f10690,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10608,f7318])).
% 13.27/2.11  fof(f10608,plain,(
% 13.27/2.11    ( ! [X0] : (~r2_hidden(sK1,k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(X0,X0))))) ) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f541,f9421,f150])).
% 13.27/2.11  fof(f10689,plain,(
% 13.27/2.11    ~spl6_120 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10688,f9419,f10657])).
% 13.27/2.11  fof(f10688,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10610,f6033])).
% 13.27/2.11  fof(f10610,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f507,f9421,f150])).
% 13.27/2.11  fof(f10679,plain,(
% 13.27/2.11    ~spl6_122 | ~spl6_4 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10674,f9419,f169,f10676])).
% 13.27/2.11  fof(f10676,plain,(
% 13.27/2.11    spl6_122 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).
% 13.27/2.11  fof(f10674,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)))) | (~spl6_4 | spl6_115)),
% 13.27/2.11    inference(forward_demodulation,[],[f10673,f1116])).
% 13.27/2.11  fof(f10673,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))))) | (~spl6_4 | spl6_115)),
% 13.27/2.11    inference(forward_demodulation,[],[f10622,f113])).
% 13.27/2.11  fof(f10622,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))))) | (~spl6_4 | spl6_115)),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f205,f9421,f289])).
% 13.27/2.11  fof(f289,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) | r2_hidden(X2,X0) | r2_hidden(X2,k4_xboole_0(X0,X1))) )),
% 13.27/2.11    inference(superposition,[],[f150,f113])).
% 13.27/2.11  fof(f205,plain,(
% 13.27/2.11    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,k1_zfmisc_1(sK0)))) ) | ~spl6_4),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f171,f132])).
% 13.27/2.11  fof(f10670,plain,(
% 13.27/2.11    ~spl6_121 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10665,f9419,f10667])).
% 13.27/2.11  fof(f10667,plain,(
% 13.27/2.11    spl6_121 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).
% 13.27/2.11  fof(f10665,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10664,f1116])).
% 13.27/2.11  fof(f10664,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK1)),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK1))))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10624,f113])).
% 13.27/2.11  fof(f10624,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK1)),k4_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))))) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f460,f9421,f289])).
% 13.27/2.11  fof(f460,plain,(
% 13.27/2.11    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(X0)))) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f161,f132])).
% 13.27/2.11  fof(f10660,plain,(
% 13.27/2.11    ~spl6_120 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10655,f9419,f10657])).
% 13.27/2.11  fof(f10655,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10654,f6033])).
% 13.27/2.11  fof(f10654,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(forward_demodulation,[],[f10628,f5434])).
% 13.27/2.11  fof(f5434,plain,(
% 13.27/2.11    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,X0)) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f178,f461,f144])).
% 13.27/2.11  fof(f144,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f117,f114])).
% 13.27/2.11  fof(f117,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(definition_unfolding,[],[f89,f111])).
% 13.27/2.11  fof(f89,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(cnf_transformation,[],[f36])).
% 13.27/2.11  fof(f36,plain,(
% 13.27/2.11    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.27/2.11    inference(flattening,[],[f35])).
% 13.27/2.11  fof(f35,plain,(
% 13.27/2.11    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 13.27/2.11    inference(ennf_transformation,[],[f26])).
% 13.27/2.11  fof(f26,axiom,(
% 13.27/2.11    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 13.27/2.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 13.27/2.11  fof(f461,plain,(
% 13.27/2.11    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f61,f161,f72])).
% 13.27/2.11  fof(f178,plain,(
% 13.27/2.11    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f61,f160,f72])).
% 13.27/2.11  fof(f160,plain,(
% 13.27/2.11    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f62,f126])).
% 13.27/2.11  fof(f10628,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f507,f178,f461,f9421,f310])).
% 13.27/2.11  fof(f310,plain,(
% 13.27/2.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k4_subset_1(X2,X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 13.27/2.11    inference(superposition,[],[f150,f144])).
% 13.27/2.11  fof(f10652,plain,(
% 13.27/2.11    ~spl6_118 | ~spl6_4 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10630,f9419,f169,f10643])).
% 13.27/2.11  fof(f10643,plain,(
% 13.27/2.11    spl6_118 <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).
% 13.27/2.11  fof(f10630,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | spl6_115)),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f171,f9421,f543])).
% 13.27/2.11  fof(f10651,plain,(
% 13.27/2.11    ~spl6_119 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10631,f9419,f10648])).
% 13.27/2.11  fof(f10648,plain,(
% 13.27/2.11    spl6_119 <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).
% 13.27/2.11  fof(f10631,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_xboole_0)) | spl6_115),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f161,f9421,f543])).
% 13.27/2.11  fof(f10646,plain,(
% 13.27/2.11    ~spl6_118 | ~spl6_29 | spl6_115),
% 13.27/2.11    inference(avatar_split_clause,[],[f10641,f9419,f805,f10643])).
% 13.27/2.11  fof(f10641,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_29 | spl6_115)),
% 13.27/2.11    inference(forward_demodulation,[],[f10635,f1231])).
% 13.27/2.11  fof(f10635,plain,(
% 13.27/2.11    ~r1_tarski(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_xboole_0)) | (~spl6_29 | spl6_115)),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f807,f9421,f543])).
% 13.27/2.11  fof(f10534,plain,(
% 13.27/2.11    ~spl6_117 | spl6_14),
% 13.27/2.11    inference(avatar_split_clause,[],[f10477,f329,f10531])).
% 13.27/2.11  fof(f10531,plain,(
% 13.27/2.11    spl6_117 <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).
% 13.27/2.11  fof(f329,plain,(
% 13.27/2.11    spl6_14 <=> r2_hidden(sK0,k1_zfmisc_1(sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 13.27/2.11  fof(f10477,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) | spl6_14),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f161,f331,f543])).
% 13.27/2.11  fof(f331,plain,(
% 13.27/2.11    ~r2_hidden(sK0,k1_zfmisc_1(sK1)) | spl6_14),
% 13.27/2.11    inference(avatar_component_clause,[],[f329])).
% 13.27/2.11  fof(f9954,plain,(
% 13.27/2.11    ~spl6_116 | ~spl6_4),
% 13.27/2.11    inference(avatar_split_clause,[],[f9953,f169,f9946])).
% 13.27/2.11  fof(f9946,plain,(
% 13.27/2.11    spl6_116 <=> r1_tarski(k1_zfmisc_1(sK0),k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).
% 13.27/2.11  fof(f9953,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK0),k1_xboole_0) | ~spl6_4),
% 13.27/2.11    inference(forward_demodulation,[],[f9931,f7318])).
% 13.27/2.11  fof(f9931,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f171,f551])).
% 13.27/2.11  fof(f551,plain,(
% 13.27/2.11    ( ! [X10,X9] : (~r1_tarski(X9,k4_xboole_0(X9,X9)) | ~r2_hidden(X10,X9)) )),
% 13.27/2.11    inference(superposition,[],[f203,f199])).
% 13.27/2.11  fof(f9949,plain,(
% 13.27/2.11    ~spl6_116 | ~spl6_29),
% 13.27/2.11    inference(avatar_split_clause,[],[f9944,f805,f9946])).
% 13.27/2.11  fof(f9944,plain,(
% 13.27/2.11    ~r1_tarski(k1_zfmisc_1(sK0),k1_xboole_0) | ~spl6_29),
% 13.27/2.11    inference(forward_demodulation,[],[f9943,f1231])).
% 13.27/2.11  fof(f9943,plain,(
% 13.27/2.11    ~r1_tarski(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0) | ~spl6_29),
% 13.27/2.11    inference(forward_demodulation,[],[f9935,f7318])).
% 13.27/2.11  fof(f9935,plain,(
% 13.27/2.11    ~r1_tarski(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))) | ~spl6_29),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f807,f551])).
% 13.27/2.11  fof(f9422,plain,(
% 13.27/2.11    ~spl6_115 | spl6_43 | ~spl6_71),
% 13.27/2.11    inference(avatar_split_clause,[],[f9417,f5058,f3904,f9419])).
% 13.27/2.11  fof(f9417,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | (spl6_43 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f9416,f5060])).
% 13.27/2.11  fof(f9416,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK1,sK0))) | spl6_43),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f3906,f127])).
% 13.27/2.11  fof(f6174,plain,(
% 13.27/2.11    ~spl6_114 | spl6_67),
% 13.27/2.11    inference(avatar_split_clause,[],[f6169,f4524,f6171])).
% 13.27/2.11  fof(f6171,plain,(
% 13.27/2.11    spl6_114 <=> r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).
% 13.27/2.11  fof(f4524,plain,(
% 13.27/2.11    spl6_67 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 13.27/2.11  fof(f6169,plain,(
% 13.27/2.11    ~r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | spl6_67),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f4526,f127])).
% 13.27/2.11  fof(f4526,plain,(
% 13.27/2.11    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | spl6_67),
% 13.27/2.11    inference(avatar_component_clause,[],[f4524])).
% 13.27/2.11  fof(f6151,plain,(
% 13.27/2.11    spl6_113),
% 13.27/2.11    inference(avatar_split_clause,[],[f6150,f6020])).
% 13.27/2.11  fof(f6020,plain,(
% 13.27/2.11    spl6_113 <=> k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).
% 13.27/2.11  fof(f6150,plain,(
% 13.27/2.11    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 13.27/2.11    inference(forward_demodulation,[],[f6149,f499])).
% 13.27/2.11  fof(f6149,plain,(
% 13.27/2.11    ( ! [X182,X183] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X183),X182))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f5989,f472])).
% 13.27/2.11  fof(f472,plain,(
% 13.27/2.11    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 13.27/2.11    inference(superposition,[],[f198,f113])).
% 13.27/2.11  fof(f5989,plain,(
% 13.27/2.11    ( ! [X182,X183] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X183),X182)) = k3_tarski(k6_enumset1(k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k4_xboole_0(X183,k4_xboole_0(X183,k1_xboole_0)),k1_xboole_0))) )),
% 13.27/2.11    inference(superposition,[],[f361,f499])).
% 13.27/2.11  fof(f361,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k3_tarski(k6_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) )),
% 13.27/2.11    inference(superposition,[],[f116,f113])).
% 13.27/2.11  fof(f6108,plain,(
% 13.27/2.11    spl6_113),
% 13.27/2.11    inference(avatar_split_clause,[],[f6107,f6020])).
% 13.27/2.11  fof(f6107,plain,(
% 13.27/2.11    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 13.27/2.11    inference(forward_demodulation,[],[f6106,f499])).
% 13.27/2.11  fof(f6106,plain,(
% 13.27/2.11    ( ! [X132,X133] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X132,X133))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f5961,f472])).
% 13.27/2.11  fof(f5961,plain,(
% 13.27/2.11    ( ! [X132,X133] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X132,X133)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(X133,k4_xboole_0(X133,k1_xboole_0))))) )),
% 13.27/2.11    inference(superposition,[],[f367,f499])).
% 13.27/2.11  fof(f367,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X2,X1)) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 13.27/2.11    inference(superposition,[],[f116,f113])).
% 13.27/2.11  fof(f6103,plain,(
% 13.27/2.11    spl6_113),
% 13.27/2.11    inference(avatar_split_clause,[],[f6102,f6020])).
% 13.27/2.11  fof(f6102,plain,(
% 13.27/2.11    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 13.27/2.11    inference(forward_demodulation,[],[f6101,f499])).
% 13.27/2.11  fof(f6101,plain,(
% 13.27/2.11    ( ! [X128,X129] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X128,k4_xboole_0(k1_xboole_0,X129)))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f5959,f499])).
% 13.27/2.11  fof(f5959,plain,(
% 13.27/2.11    ( ! [X128,X129] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X128,k4_xboole_0(k1_xboole_0,X129))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X129,k4_xboole_0(X129,k1_xboole_0)))))) )),
% 13.27/2.11    inference(superposition,[],[f364,f499])).
% 13.27/2.11  fof(f364,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) )),
% 13.27/2.11    inference(superposition,[],[f116,f113])).
% 13.27/2.11  fof(f6098,plain,(
% 13.27/2.11    spl6_113),
% 13.27/2.11    inference(avatar_split_clause,[],[f6097,f6020])).
% 13.27/2.11  fof(f6097,plain,(
% 13.27/2.11    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 13.27/2.11    inference(forward_demodulation,[],[f6096,f499])).
% 13.27/2.11  fof(f6096,plain,(
% 13.27/2.11    ( ! [X125,X124] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X125),X124))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f6095,f472])).
% 13.27/2.11  fof(f6095,plain,(
% 13.27/2.11    ( ! [X125,X124] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X125),X124)) = k3_tarski(k6_enumset1(k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k1_xboole_0))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f5957,f6033])).
% 13.27/2.11  fof(f5957,plain,(
% 13.27/2.11    ( ! [X125,X124] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X125),X124)) = k3_tarski(k6_enumset1(k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(X125,k4_xboole_0(X125,k1_xboole_0)),k4_xboole_0(k1_xboole_0,k1_xboole_0)))) )),
% 13.27/2.11    inference(superposition,[],[f361,f499])).
% 13.27/2.11  fof(f6023,plain,(
% 13.27/2.11    spl6_113),
% 13.27/2.11    inference(avatar_split_clause,[],[f6018,f6020])).
% 13.27/2.11  fof(f6018,plain,(
% 13.27/2.11    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 13.27/2.11    inference(forward_demodulation,[],[f6017,f499])).
% 13.27/2.11  fof(f6017,plain,(
% 13.27/2.11    ( ! [X6,X7] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))) )),
% 13.27/2.11    inference(forward_demodulation,[],[f5899,f499])).
% 13.27/2.11  fof(f5899,plain,(
% 13.27/2.11    ( ! [X6,X7] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))))) )),
% 13.27/2.11    inference(superposition,[],[f116,f499])).
% 13.27/2.11  fof(f5876,plain,(
% 13.27/2.11    spl6_112 | ~spl6_104),
% 13.27/2.11    inference(avatar_split_clause,[],[f5871,f5745,f5873])).
% 13.27/2.11  fof(f5873,plain,(
% 13.27/2.11    spl6_112 <=> k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).
% 13.27/2.11  fof(f5745,plain,(
% 13.27/2.11    spl6_104 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 13.27/2.11  fof(f5871,plain,(
% 13.27/2.11    k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_104),
% 13.27/2.11    inference(forward_demodulation,[],[f5747,f5833])).
% 13.27/2.11  fof(f5833,plain,(
% 13.27/2.11    ( ! [X0] : (k4_subset_1(X0,X0,X0) = X0) )),
% 13.27/2.11    inference(forward_demodulation,[],[f5435,f526])).
% 13.27/2.11  fof(f5435,plain,(
% 13.27/2.11    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_subset_1(X0,X0,X0)) )),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f461,f461,f144])).
% 13.27/2.11  fof(f5747,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_104),
% 13.27/2.11    inference(avatar_component_clause,[],[f5745])).
% 13.27/2.11  fof(f5869,plain,(
% 13.27/2.11    spl6_110 | ~spl6_2 | ~spl6_71),
% 13.27/2.11    inference(avatar_split_clause,[],[f5868,f5058,f140,f5856])).
% 13.27/2.11  fof(f5856,plain,(
% 13.27/2.11    spl6_110 <=> sK0 = k4_subset_1(sK0,sK0,sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 13.27/2.11  fof(f140,plain,(
% 13.27/2.11    spl6_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 13.27/2.11  fof(f5868,plain,(
% 13.27/2.11    sK0 = k4_subset_1(sK0,sK0,sK1) | (~spl6_2 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5867,f64])).
% 13.27/2.11  fof(f5867,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | (~spl6_2 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5424,f5060])).
% 13.27/2.11  fof(f5424,plain,(
% 13.27/2.11    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k4_subset_1(sK0,sK0,sK1) | ~spl6_2),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f142,f461,f144])).
% 13.27/2.11  fof(f142,plain,(
% 13.27/2.11    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl6_2),
% 13.27/2.11    inference(avatar_component_clause,[],[f140])).
% 13.27/2.11  fof(f5866,plain,(
% 13.27/2.11    spl6_111 | ~spl6_6 | ~spl6_8),
% 13.27/2.11    inference(avatar_split_clause,[],[f5865,f225,f193,f5861])).
% 13.27/2.11  fof(f5861,plain,(
% 13.27/2.11    spl6_111 <=> k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 13.27/2.11  fof(f193,plain,(
% 13.27/2.11    spl6_6 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 13.27/2.11  fof(f225,plain,(
% 13.27/2.11    spl6_8 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 13.27/2.11  fof(f5865,plain,(
% 13.27/2.11    k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.27/2.11    inference(forward_demodulation,[],[f5425,f227])).
% 13.27/2.11  fof(f227,plain,(
% 13.27/2.11    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl6_8),
% 13.27/2.11    inference(avatar_component_clause,[],[f225])).
% 13.27/2.11  fof(f5425,plain,(
% 13.27/2.11    k5_xboole_0(sK0,k4_xboole_0(k3_subset_1(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f195,f461,f144])).
% 13.27/2.11  fof(f195,plain,(
% 13.27/2.11    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_6),
% 13.27/2.11    inference(avatar_component_clause,[],[f193])).
% 13.27/2.11  fof(f5864,plain,(
% 13.27/2.11    spl6_111 | ~spl6_22),
% 13.27/2.11    inference(avatar_split_clause,[],[f5426,f435,f5861])).
% 13.27/2.11  fof(f435,plain,(
% 13.27/2.11    spl6_22 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 13.27/2.11  fof(f5426,plain,(
% 13.27/2.11    k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f437,f461,f144])).
% 13.27/2.11  fof(f437,plain,(
% 13.27/2.11    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_22),
% 13.27/2.11    inference(avatar_component_clause,[],[f435])).
% 13.27/2.11  fof(f5859,plain,(
% 13.27/2.11    spl6_110 | ~spl6_21 | ~spl6_28 | ~spl6_71),
% 13.27/2.11    inference(avatar_split_clause,[],[f5854,f5058,f707,f427,f5856])).
% 13.27/2.11  fof(f427,plain,(
% 13.27/2.11    spl6_21 <=> m1_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 13.27/2.11  fof(f5854,plain,(
% 13.27/2.11    sK0 = k4_subset_1(sK0,sK0,sK1) | (~spl6_21 | ~spl6_28 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5853,f64])).
% 13.27/2.11  fof(f5853,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | (~spl6_21 | ~spl6_28 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5852,f5060])).
% 13.27/2.11  fof(f5852,plain,(
% 13.27/2.11    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k4_subset_1(sK0,sK0,sK1) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5427,f709])).
% 13.27/2.11  fof(f5427,plain,(
% 13.27/2.11    k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) = k4_subset_1(sK0,sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f429,f461,f144])).
% 13.27/2.11  fof(f429,plain,(
% 13.27/2.11    m1_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_21),
% 13.27/2.11    inference(avatar_component_clause,[],[f427])).
% 13.27/2.11  fof(f5848,plain,(
% 13.27/2.11    spl6_107 | ~spl6_2),
% 13.27/2.11    inference(avatar_split_clause,[],[f5430,f140,f5821])).
% 13.27/2.11  fof(f5821,plain,(
% 13.27/2.11    spl6_107 <=> k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).
% 13.27/2.11  fof(f5430,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl6_2),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f142,f461,f144])).
% 13.27/2.11  fof(f5847,plain,(
% 13.27/2.11    spl6_108 | ~spl6_6 | ~spl6_8 | ~spl6_71),
% 13.27/2.11    inference(avatar_split_clause,[],[f5846,f5058,f225,f193,f5829])).
% 13.27/2.11  fof(f5829,plain,(
% 13.27/2.11    spl6_108 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).
% 13.27/2.11  fof(f5846,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5845,f5060])).
% 13.27/2.11  fof(f5845,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | (~spl6_6 | ~spl6_8)),
% 13.27/2.11    inference(forward_demodulation,[],[f5844,f1116])).
% 13.27/2.11  fof(f5844,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl6_6 | ~spl6_8)),
% 13.27/2.11    inference(forward_demodulation,[],[f5431,f227])).
% 13.27/2.11  fof(f5431,plain,(
% 13.27/2.11    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK0) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k3_subset_1(sK0,sK1))) | ~spl6_6),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f195,f461,f144])).
% 13.27/2.11  fof(f5843,plain,(
% 13.27/2.11    spl6_108 | ~spl6_22 | ~spl6_71),
% 13.27/2.11    inference(avatar_split_clause,[],[f5842,f5058,f435,f5829])).
% 13.27/2.11  fof(f5842,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0) | (~spl6_22 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5841,f5060])).
% 13.27/2.11  fof(f5841,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl6_22),
% 13.27/2.11    inference(forward_demodulation,[],[f5432,f1116])).
% 13.27/2.11  fof(f5432,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_22),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f437,f461,f144])).
% 13.27/2.11  fof(f5840,plain,(
% 13.27/2.11    spl6_109 | ~spl6_21 | ~spl6_28),
% 13.27/2.11    inference(avatar_split_clause,[],[f5835,f707,f427,f5837])).
% 13.27/2.11  fof(f5837,plain,(
% 13.27/2.11    spl6_109 <=> k4_subset_1(sK0,sK1,sK0) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).
% 13.27/2.11  fof(f5835,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK0) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5834,f709])).
% 13.27/2.11  fof(f5834,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | ~spl6_21),
% 13.27/2.11    inference(forward_demodulation,[],[f5433,f1116])).
% 13.27/2.11  fof(f5433,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl6_21),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f429,f461,f144])).
% 13.27/2.11  fof(f5832,plain,(
% 13.27/2.11    spl6_108 | ~spl6_22 | ~spl6_71),
% 13.27/2.11    inference(avatar_split_clause,[],[f5827,f5058,f435,f5829])).
% 13.27/2.11  fof(f5827,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k1_xboole_0) | (~spl6_22 | ~spl6_71)),
% 13.27/2.11    inference(forward_demodulation,[],[f5826,f5060])).
% 13.27/2.11  fof(f5826,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl6_22),
% 13.27/2.11    inference(forward_demodulation,[],[f5825,f1116])).
% 13.27/2.11  fof(f5825,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_22),
% 13.27/2.11    inference(forward_demodulation,[],[f5438,f113])).
% 13.27/2.11  fof(f5438,plain,(
% 13.27/2.11    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK0) | ~spl6_22),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f437,f461,f306])).
% 13.27/2.11  fof(f306,plain,(
% 13.27/2.11    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_subset_1(X2,k4_xboole_0(X0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X2))) )),
% 13.27/2.11    inference(superposition,[],[f144,f113])).
% 13.27/2.11  fof(f5824,plain,(
% 13.27/2.11    spl6_107 | ~spl6_21 | ~spl6_28),
% 13.27/2.11    inference(avatar_split_clause,[],[f5819,f707,f427,f5821])).
% 13.27/2.11  fof(f5819,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5818,f709])).
% 13.27/2.11  fof(f5818,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5817,f113])).
% 13.27/2.11  fof(f5817,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5439,f709])).
% 13.27/2.11  fof(f5439,plain,(
% 13.27/2.11    k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | ~spl6_21),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f429,f461,f306])).
% 13.27/2.11  fof(f5816,plain,(
% 13.27/2.11    spl6_105 | ~spl6_2 | ~spl6_88),
% 13.27/2.11    inference(avatar_split_clause,[],[f5815,f5388,f140,f5766])).
% 13.27/2.11  fof(f5766,plain,(
% 13.27/2.11    spl6_105 <=> sK1 = k4_subset_1(sK1,sK1,k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).
% 13.27/2.11  fof(f5388,plain,(
% 13.27/2.11    spl6_88 <=> sK1 = k4_subset_1(sK0,sK1,k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 13.27/2.11  fof(f5815,plain,(
% 13.27/2.11    sK1 = k4_subset_1(sK1,sK1,k1_xboole_0) | (~spl6_2 | ~spl6_88)),
% 13.27/2.11    inference(forward_demodulation,[],[f5440,f5390])).
% 13.27/2.11  fof(f5390,plain,(
% 13.27/2.11    sK1 = k4_subset_1(sK0,sK1,k1_xboole_0) | ~spl6_88),
% 13.27/2.11    inference(avatar_component_clause,[],[f5388])).
% 13.27/2.11  fof(f5440,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0) | ~spl6_2),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f178,f178,f142,f461,f309])).
% 13.27/2.11  fof(f309,plain,(
% 13.27/2.11    ( ! [X2,X0,X3,X1] : (k4_subset_1(X2,X0,X1) = k4_subset_1(X3,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X3)) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 13.27/2.11    inference(superposition,[],[f144,f144])).
% 13.27/2.11  fof(f5814,plain,(
% 13.27/2.11    spl6_92 | ~spl6_2 | ~spl6_61),
% 13.27/2.11    inference(avatar_split_clause,[],[f5813,f4093,f140,f5616])).
% 13.27/2.11  fof(f5616,plain,(
% 13.27/2.11    spl6_92 <=> sK1 = k4_subset_1(sK1,sK1,sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 13.27/2.11  fof(f4093,plain,(
% 13.27/2.11    spl6_61 <=> sK1 = k4_subset_1(sK0,sK1,sK1)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 13.27/2.11  fof(f5813,plain,(
% 13.27/2.11    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_2 | ~spl6_61)),
% 13.27/2.11    inference(forward_demodulation,[],[f5441,f4095])).
% 13.27/2.11  fof(f4095,plain,(
% 13.27/2.11    sK1 = k4_subset_1(sK0,sK1,sK1) | ~spl6_61),
% 13.27/2.11    inference(avatar_component_clause,[],[f4093])).
% 13.27/2.11  fof(f5441,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | ~spl6_2),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f142,f461,f142,f461,f309])).
% 13.27/2.11  fof(f5812,plain,(
% 13.27/2.11    spl6_106 | ~spl6_6 | ~spl6_8 | ~spl6_89),
% 13.27/2.11    inference(avatar_split_clause,[],[f5811,f5395,f225,f193,f5772])).
% 13.27/2.11  fof(f5772,plain,(
% 13.27/2.11    spl6_106 <=> k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).
% 13.27/2.11  fof(f5395,plain,(
% 13.27/2.11    spl6_89 <=> k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 13.27/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 13.27/2.11  fof(f5811,plain,(
% 13.27/2.11    k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_89)),
% 13.27/2.11    inference(forward_demodulation,[],[f5810,f5397])).
% 13.27/2.11  fof(f5397,plain,(
% 13.27/2.11    k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_89),
% 13.27/2.11    inference(avatar_component_clause,[],[f5395])).
% 13.27/2.11  fof(f5810,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 13.27/2.11    inference(forward_demodulation,[],[f5442,f227])).
% 13.27/2.11  fof(f5442,plain,(
% 13.27/2.11    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k1_xboole_0) | ~spl6_6),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f178,f178,f195,f461,f309])).
% 13.27/2.11  fof(f5809,plain,(
% 13.27/2.11    spl6_104 | ~spl6_6 | ~spl6_8),
% 13.27/2.11    inference(avatar_split_clause,[],[f5808,f225,f193,f5745])).
% 13.27/2.11  fof(f5808,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.27/2.11    inference(forward_demodulation,[],[f5443,f227])).
% 13.27/2.11  fof(f5443,plain,(
% 13.27/2.11    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f195,f461,f195,f461,f309])).
% 13.27/2.11  fof(f5807,plain,(
% 13.27/2.11    spl6_106 | ~spl6_22 | ~spl6_89),
% 13.27/2.11    inference(avatar_split_clause,[],[f5806,f5395,f435,f5772])).
% 13.27/2.11  fof(f5806,plain,(
% 13.27/2.11    k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_22 | ~spl6_89)),
% 13.27/2.11    inference(forward_demodulation,[],[f5444,f5397])).
% 13.27/2.11  fof(f5444,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_22),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f178,f178,f437,f461,f309])).
% 13.27/2.11  fof(f5805,plain,(
% 13.27/2.11    spl6_104 | ~spl6_22),
% 13.27/2.11    inference(avatar_split_clause,[],[f5445,f435,f5745])).
% 13.27/2.11  fof(f5445,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f437,f461,f437,f461,f309])).
% 13.27/2.11  fof(f5804,plain,(
% 13.27/2.11    spl6_105 | ~spl6_21 | ~spl6_28 | ~spl6_88),
% 13.27/2.11    inference(avatar_split_clause,[],[f5803,f5388,f707,f427,f5766])).
% 13.27/2.11  fof(f5803,plain,(
% 13.27/2.11    sK1 = k4_subset_1(sK1,sK1,k1_xboole_0) | (~spl6_21 | ~spl6_28 | ~spl6_88)),
% 13.27/2.11    inference(forward_demodulation,[],[f5802,f5390])).
% 13.27/2.11  fof(f5802,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5446,f709])).
% 13.27/2.11  fof(f5446,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl6_21),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f178,f178,f429,f461,f309])).
% 13.27/2.11  fof(f5801,plain,(
% 13.27/2.11    spl6_92 | ~spl6_21 | ~spl6_28 | ~spl6_61),
% 13.27/2.11    inference(avatar_split_clause,[],[f5800,f4093,f707,f427,f5616])).
% 13.27/2.11  fof(f5800,plain,(
% 13.27/2.11    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28 | ~spl6_61)),
% 13.27/2.11    inference(forward_demodulation,[],[f5799,f4095])).
% 13.27/2.11  fof(f5799,plain,(
% 13.27/2.11    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28)),
% 13.27/2.11    inference(forward_demodulation,[],[f5447,f709])).
% 13.27/2.11  fof(f5447,plain,(
% 13.27/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.27/2.11    inference(unit_resulting_resolution,[],[f429,f461,f429,f461,f309])).
% 13.27/2.11  fof(f5796,plain,(
% 13.27/2.11    spl6_102 | ~spl6_2),
% 13.27/2.11    inference(avatar_split_clause,[],[f5464,f140,f5729])).
% 13.46/2.11  fof(f5729,plain,(
% 13.46/2.11    spl6_102 <=> k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1)),
% 13.46/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 13.46/2.11  fof(f5464,plain,(
% 13.46/2.11    k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1) | ~spl6_2),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f142,f178,f178,f461,f309])).
% 13.46/2.11  fof(f5795,plain,(
% 13.46/2.11    spl6_103 | ~spl6_6 | ~spl6_8),
% 13.46/2.11    inference(avatar_split_clause,[],[f5794,f225,f193,f5734])).
% 13.46/2.11  fof(f5734,plain,(
% 13.46/2.11    spl6_103 <=> k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 13.46/2.11    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).
% 13.46/2.11  fof(f5794,plain,(
% 13.46/2.11    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.11    inference(forward_demodulation,[],[f5465,f227])).
% 13.46/2.11  fof(f5465,plain,(
% 13.46/2.11    k4_subset_1(sK0,k1_xboole_0,k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k1_xboole_0,k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f195,f178,f178,f461,f309])).
% 13.46/2.11  fof(f5793,plain,(
% 13.46/2.11    spl6_103 | ~spl6_22),
% 13.46/2.11    inference(avatar_split_clause,[],[f5466,f435,f5734])).
% 13.46/2.11  fof(f5466,plain,(
% 13.46/2.11    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f437,f178,f178,f461,f309])).
% 13.46/2.11  fof(f5792,plain,(
% 13.46/2.11    spl6_102 | ~spl6_21 | ~spl6_28),
% 13.46/2.11    inference(avatar_split_clause,[],[f5791,f707,f427,f5729])).
% 13.46/2.11  fof(f5791,plain,(
% 13.46/2.11    k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.11    inference(forward_demodulation,[],[f5467,f709])).
% 13.46/2.11  fof(f5467,plain,(
% 13.46/2.11    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f429,f178,f178,f461,f309])).
% 13.46/2.11  fof(f5789,plain,(
% 13.46/2.11    spl6_92 | ~spl6_2 | ~spl6_61),
% 13.46/2.11    inference(avatar_split_clause,[],[f5788,f4093,f140,f5616])).
% 13.46/2.11  fof(f5788,plain,(
% 13.46/2.11    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_2 | ~spl6_61)),
% 13.46/2.11    inference(forward_demodulation,[],[f5472,f4095])).
% 13.46/2.11  fof(f5472,plain,(
% 13.46/2.11    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | ~spl6_2),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f142,f142,f461,f461,f309])).
% 13.46/2.11  fof(f5787,plain,(
% 13.46/2.11    spl6_104 | ~spl6_6 | ~spl6_8),
% 13.46/2.11    inference(avatar_split_clause,[],[f5786,f225,f193,f5745])).
% 13.46/2.11  fof(f5786,plain,(
% 13.46/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.11    inference(forward_demodulation,[],[f5473,f227])).
% 13.46/2.11  fof(f5473,plain,(
% 13.46/2.11    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f195,f195,f461,f461,f309])).
% 13.46/2.11  fof(f5785,plain,(
% 13.46/2.11    spl6_104 | ~spl6_22),
% 13.46/2.11    inference(avatar_split_clause,[],[f5474,f435,f5745])).
% 13.46/2.11  fof(f5474,plain,(
% 13.46/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f437,f437,f461,f461,f309])).
% 13.46/2.11  fof(f5784,plain,(
% 13.46/2.11    spl6_92 | ~spl6_21 | ~spl6_28 | ~spl6_61),
% 13.46/2.11    inference(avatar_split_clause,[],[f5783,f4093,f707,f427,f5616])).
% 13.46/2.11  fof(f5783,plain,(
% 13.46/2.11    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28 | ~spl6_61)),
% 13.46/2.11    inference(forward_demodulation,[],[f5782,f4095])).
% 13.46/2.11  fof(f5782,plain,(
% 13.46/2.11    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.11    inference(forward_demodulation,[],[f5475,f709])).
% 13.46/2.11  fof(f5475,plain,(
% 13.46/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f429,f429,f461,f461,f309])).
% 13.46/2.11  fof(f5780,plain,(
% 13.46/2.11    spl6_105 | ~spl6_2 | ~spl6_88),
% 13.46/2.11    inference(avatar_split_clause,[],[f5779,f5388,f140,f5766])).
% 13.46/2.11  fof(f5779,plain,(
% 13.46/2.11    sK1 = k4_subset_1(sK1,sK1,k1_xboole_0) | (~spl6_2 | ~spl6_88)),
% 13.46/2.11    inference(forward_demodulation,[],[f5484,f5390])).
% 13.46/2.11  fof(f5484,plain,(
% 13.46/2.11    k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0) | ~spl6_2),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f142,f178,f178,f461,f309])).
% 13.46/2.11  fof(f5778,plain,(
% 13.46/2.11    spl6_106 | ~spl6_6 | ~spl6_8 | ~spl6_89),
% 13.46/2.11    inference(avatar_split_clause,[],[f5777,f5395,f225,f193,f5772])).
% 13.46/2.11  fof(f5777,plain,(
% 13.46/2.11    k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_6 | ~spl6_8 | ~spl6_89)),
% 13.46/2.11    inference(forward_demodulation,[],[f5776,f5397])).
% 13.46/2.11  fof(f5776,plain,(
% 13.46/2.11    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 13.46/2.11    inference(forward_demodulation,[],[f5485,f227])).
% 13.46/2.11  fof(f5485,plain,(
% 13.46/2.11    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k1_xboole_0) | ~spl6_6),
% 13.46/2.11    inference(unit_resulting_resolution,[],[f195,f178,f178,f461,f309])).
% 13.46/2.11  fof(f5775,plain,(
% 13.46/2.11    spl6_106 | ~spl6_22 | ~spl6_89),
% 13.46/2.11    inference(avatar_split_clause,[],[f5770,f5395,f435,f5772])).
% 13.46/2.11  fof(f5770,plain,(
% 13.46/2.11    k4_xboole_0(sK0,sK1) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_22 | ~spl6_89)),
% 13.46/2.11    inference(forward_demodulation,[],[f5486,f5397])).
% 13.46/2.12  fof(f5486,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_22),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f178,f178,f461,f309])).
% 13.46/2.12  fof(f5769,plain,(
% 13.46/2.12    spl6_105 | ~spl6_21 | ~spl6_28 | ~spl6_88),
% 13.46/2.12    inference(avatar_split_clause,[],[f5764,f5388,f707,f427,f5766])).
% 13.46/2.12  fof(f5764,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK1,sK1,k1_xboole_0) | (~spl6_21 | ~spl6_28 | ~spl6_88)),
% 13.46/2.12    inference(forward_demodulation,[],[f5763,f5390])).
% 13.46/2.12  fof(f5763,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5487,f709])).
% 13.46/2.12  fof(f5487,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f178,f178,f461,f309])).
% 13.46/2.12  fof(f5761,plain,(
% 13.46/2.12    spl6_92 | ~spl6_2 | ~spl6_61),
% 13.46/2.12    inference(avatar_split_clause,[],[f5760,f4093,f140,f5616])).
% 13.46/2.12  fof(f5760,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_2 | ~spl6_61)),
% 13.46/2.12    inference(forward_demodulation,[],[f5492,f4095])).
% 13.46/2.12  fof(f5492,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | ~spl6_2),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f142,f142,f461,f461,f309])).
% 13.46/2.12  fof(f5759,plain,(
% 13.46/2.12    spl6_104 | ~spl6_6 | ~spl6_8),
% 13.46/2.12    inference(avatar_split_clause,[],[f5758,f225,f193,f5745])).
% 13.46/2.12  fof(f5758,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.12    inference(forward_demodulation,[],[f5493,f227])).
% 13.46/2.12  fof(f5493,plain,(
% 13.46/2.12    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f195,f195,f461,f461,f309])).
% 13.46/2.12  fof(f5757,plain,(
% 13.46/2.12    spl6_104 | ~spl6_22),
% 13.46/2.12    inference(avatar_split_clause,[],[f5494,f435,f5745])).
% 13.46/2.12  fof(f5494,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f437,f461,f461,f309])).
% 13.46/2.12  fof(f5756,plain,(
% 13.46/2.12    spl6_92 | ~spl6_21 | ~spl6_28 | ~spl6_61),
% 13.46/2.12    inference(avatar_split_clause,[],[f5755,f4093,f707,f427,f5616])).
% 13.46/2.12  fof(f5755,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28 | ~spl6_61)),
% 13.46/2.12    inference(forward_demodulation,[],[f5754,f4095])).
% 13.46/2.12  fof(f5754,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5495,f709])).
% 13.46/2.12  fof(f5495,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f429,f461,f461,f309])).
% 13.46/2.12  fof(f5752,plain,(
% 13.46/2.12    spl6_92 | ~spl6_2 | ~spl6_61),
% 13.46/2.12    inference(avatar_split_clause,[],[f5751,f4093,f140,f5616])).
% 13.46/2.12  fof(f5751,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_2 | ~spl6_61)),
% 13.46/2.12    inference(forward_demodulation,[],[f5500,f4095])).
% 13.46/2.12  fof(f5500,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | ~spl6_2),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f461,f142,f142,f461,f309])).
% 13.46/2.12  fof(f5750,plain,(
% 13.46/2.12    spl6_104 | ~spl6_6 | ~spl6_8),
% 13.46/2.12    inference(avatar_split_clause,[],[f5749,f225,f193,f5745])).
% 13.46/2.12  fof(f5749,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.12    inference(forward_demodulation,[],[f5503,f227])).
% 13.46/2.12  fof(f5503,plain,(
% 13.46/2.12    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f195,f461,f195,f461,f309])).
% 13.46/2.12  fof(f5748,plain,(
% 13.46/2.12    spl6_104 | ~spl6_22),
% 13.46/2.12    inference(avatar_split_clause,[],[f5505,f435,f5745])).
% 13.46/2.12  fof(f5505,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f461,f437,f461,f309])).
% 13.46/2.12  fof(f5743,plain,(
% 13.46/2.12    spl6_92 | ~spl6_21 | ~spl6_28 | ~spl6_61),
% 13.46/2.12    inference(avatar_split_clause,[],[f5742,f4093,f707,f427,f5616])).
% 13.46/2.12  fof(f5742,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28 | ~spl6_61)),
% 13.46/2.12    inference(forward_demodulation,[],[f5741,f4095])).
% 13.46/2.12  fof(f5741,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5507,f709])).
% 13.46/2.12  fof(f5507,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f461,f429,f461,f309])).
% 13.46/2.12  fof(f5740,plain,(
% 13.46/2.12    spl6_102 | ~spl6_2),
% 13.46/2.12    inference(avatar_split_clause,[],[f5508,f140,f5729])).
% 13.46/2.12  fof(f5508,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1) | ~spl6_2),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f142,f178,f178,f461,f309])).
% 13.46/2.12  fof(f5739,plain,(
% 13.46/2.12    spl6_103 | ~spl6_6 | ~spl6_8),
% 13.46/2.12    inference(avatar_split_clause,[],[f5738,f225,f193,f5734])).
% 13.46/2.12  fof(f5738,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.12    inference(forward_demodulation,[],[f5509,f227])).
% 13.46/2.12  fof(f5509,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k3_subset_1(sK0,sK1)) = k4_subset_1(k3_subset_1(sK0,sK1),k1_xboole_0,k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f195,f178,f178,f461,f309])).
% 13.46/2.12  fof(f5737,plain,(
% 13.46/2.12    spl6_103 | ~spl6_22),
% 13.46/2.12    inference(avatar_split_clause,[],[f5510,f435,f5734])).
% 13.46/2.12  fof(f5510,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_subset_1(k4_xboole_0(sK0,sK1),k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl6_22),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f178,f178,f461,f309])).
% 13.46/2.12  fof(f5732,plain,(
% 13.46/2.12    spl6_102 | ~spl6_21 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5727,f707,f427,f5729])).
% 13.46/2.12  fof(f5727,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,sK1) = k4_subset_1(sK1,k1_xboole_0,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5511,f709])).
% 13.46/2.12  fof(f5511,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f178,f178,f461,f309])).
% 13.46/2.12  fof(f5724,plain,(
% 13.46/2.12    ~spl6_101 | spl6_14),
% 13.46/2.12    inference(avatar_split_clause,[],[f5520,f329,f5721])).
% 13.46/2.12  fof(f5721,plain,(
% 13.46/2.12    spl6_101 <=> r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 13.46/2.12  fof(f5520,plain,(
% 13.46/2.12    ~r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_xboole_0)) | spl6_14),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f331,f507,f178,f461,f310])).
% 13.46/2.12  fof(f5716,plain,(
% 13.46/2.12    ~spl6_99 | spl6_14),
% 13.46/2.12    inference(avatar_split_clause,[],[f5525,f329,f5701])).
% 13.46/2.12  fof(f5701,plain,(
% 13.46/2.12    spl6_99 <=> r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 13.46/2.12  fof(f5525,plain,(
% 13.46/2.12    ~r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_zfmisc_1(sK1))) | spl6_14),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f331,f331,f461,f461,f310])).
% 13.46/2.12  fof(f5712,plain,(
% 13.46/2.12    ~spl6_100 | spl6_14),
% 13.46/2.12    inference(avatar_split_clause,[],[f5530,f329,f5709])).
% 13.46/2.12  fof(f5709,plain,(
% 13.46/2.12    spl6_100 <=> r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_xboole_0,k1_zfmisc_1(sK1)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 13.46/2.12  fof(f5530,plain,(
% 13.46/2.12    ~r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_xboole_0,k1_zfmisc_1(sK1))) | spl6_14),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f331,f507,f178,f461,f310])).
% 13.46/2.12  fof(f5704,plain,(
% 13.46/2.12    ~spl6_99 | spl6_14),
% 13.46/2.12    inference(avatar_split_clause,[],[f5535,f329,f5701])).
% 13.46/2.12  fof(f5535,plain,(
% 13.46/2.12    ~r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1),k1_zfmisc_1(sK1))) | spl6_14),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f331,f331,f461,f461,f310])).
% 13.46/2.12  fof(f5696,plain,(
% 13.46/2.12    spl6_94 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f5541,f387,f5647])).
% 13.46/2.12  fof(f5647,plain,(
% 13.46/2.12    spl6_94 <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 13.46/2.12  fof(f387,plain,(
% 13.46/2.12    spl6_15 <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 13.46/2.12  fof(f5541,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f461,f461,f311])).
% 13.46/2.12  fof(f311,plain,(
% 13.46/2.12    ( ! [X6,X4,X7,X5] : (r2_hidden(X7,k4_subset_1(X6,X4,X5)) | ~r2_hidden(X7,X4) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 13.46/2.12    inference(superposition,[],[f149,f144])).
% 13.46/2.12  fof(f149,plain,(
% 13.46/2.12    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X0)) )),
% 13.46/2.12    inference(forward_demodulation,[],[f129,f114])).
% 13.46/2.12  fof(f129,plain,(
% 13.46/2.12    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 13.46/2.12    inference(equality_resolution,[],[f122])).
% 13.46/2.12  fof(f122,plain,(
% 13.46/2.12    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 13.46/2.12    inference(definition_unfolding,[],[f91,f111])).
% 13.46/2.12  fof(f91,plain,(
% 13.46/2.12    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 13.46/2.12    inference(cnf_transformation,[],[f53])).
% 13.46/2.12  fof(f389,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_15),
% 13.46/2.12    inference(avatar_component_clause,[],[f387])).
% 13.46/2.12  fof(f5695,plain,(
% 13.46/2.12    spl6_93 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5694,f707,f562,f5639])).
% 13.46/2.12  fof(f5639,plain,(
% 13.46/2.12    spl6_93 <=> r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 13.46/2.12  fof(f562,plain,(
% 13.46/2.12    spl6_24 <=> r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 13.46/2.12  fof(f5694,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5542,f709])).
% 13.46/2.12  fof(f5542,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f461,f461,f311])).
% 13.46/2.12  fof(f564,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_24),
% 13.46/2.12    inference(avatar_component_clause,[],[f562])).
% 13.46/2.12  fof(f5693,plain,(
% 13.46/2.12    spl6_93 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f5544,f169,f5639])).
% 13.46/2.12  fof(f5544,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f461,f461,f311])).
% 13.46/2.12  fof(f5692,plain,(
% 13.46/2.12    spl6_93 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5691,f805,f5639])).
% 13.46/2.12  fof(f5691,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f5548,f1231])).
% 13.46/2.12  fof(f5548,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f461,f461,f311])).
% 13.46/2.12  fof(f5690,plain,(
% 13.46/2.12    spl6_98 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f5550,f387,f5687])).
% 13.46/2.12  fof(f5687,plain,(
% 13.46/2.12    spl6_98 <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 13.46/2.12  fof(f5550,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f178,f461,f311])).
% 13.46/2.12  fof(f5685,plain,(
% 13.46/2.12    spl6_97 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5684,f707,f562,f5679])).
% 13.46/2.12  fof(f5679,plain,(
% 13.46/2.12    spl6_97 <=> r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 13.46/2.12  fof(f5684,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5551,f709])).
% 13.46/2.12  fof(f5551,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f178,f461,f311])).
% 13.46/2.12  fof(f5683,plain,(
% 13.46/2.12    spl6_97 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f5553,f169,f5679])).
% 13.46/2.12  fof(f5553,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f178,f461,f311])).
% 13.46/2.12  fof(f5682,plain,(
% 13.46/2.12    spl6_97 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5677,f805,f5679])).
% 13.46/2.12  fof(f5677,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f5557,f1231])).
% 13.46/2.12  fof(f5557,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0)) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f178,f461,f311])).
% 13.46/2.12  fof(f5676,plain,(
% 13.46/2.12    spl6_94 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f5559,f387,f5647])).
% 13.46/2.12  fof(f5559,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f461,f461,f311])).
% 13.46/2.12  fof(f5675,plain,(
% 13.46/2.12    spl6_93 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5674,f707,f562,f5639])).
% 13.46/2.12  fof(f5674,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5560,f709])).
% 13.46/2.12  fof(f5560,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f461,f461,f311])).
% 13.46/2.12  fof(f5673,plain,(
% 13.46/2.12    spl6_93 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f5562,f169,f5639])).
% 13.46/2.12  fof(f5562,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f461,f461,f311])).
% 13.46/2.12  fof(f5672,plain,(
% 13.46/2.12    spl6_93 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5671,f805,f5639])).
% 13.46/2.12  fof(f5671,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f5566,f1231])).
% 13.46/2.12  fof(f5566,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f461,f461,f311])).
% 13.46/2.12  fof(f5670,plain,(
% 13.46/2.12    spl6_96 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f5568,f387,f5667])).
% 13.46/2.12  fof(f5667,plain,(
% 13.46/2.12    spl6_96 <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 13.46/2.12  fof(f5568,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f178,f461,f312])).
% 13.46/2.12  fof(f312,plain,(
% 13.46/2.12    ( ! [X10,X8,X11,X9] : (r2_hidden(X11,k4_subset_1(X10,X8,X9)) | ~r2_hidden(X11,X9) | ~m1_subset_1(X9,k1_zfmisc_1(X10)) | ~m1_subset_1(X8,k1_zfmisc_1(X10))) )),
% 13.46/2.12    inference(superposition,[],[f148,f144])).
% 13.46/2.12  fof(f5665,plain,(
% 13.46/2.12    spl6_95 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5664,f707,f562,f5659])).
% 13.46/2.12  fof(f5659,plain,(
% 13.46/2.12    spl6_95 <=> r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 13.46/2.12  fof(f5664,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5569,f709])).
% 13.46/2.12  fof(f5569,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f178,f461,f312])).
% 13.46/2.12  fof(f5663,plain,(
% 13.46/2.12    spl6_95 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f5571,f169,f5659])).
% 13.46/2.12  fof(f5571,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f178,f461,f312])).
% 13.46/2.12  fof(f5662,plain,(
% 13.46/2.12    spl6_95 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5657,f805,f5659])).
% 13.46/2.12  fof(f5657,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_xboole_0,k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f5575,f1231])).
% 13.46/2.12  fof(f5575,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f178,f461,f312])).
% 13.46/2.12  fof(f5656,plain,(
% 13.46/2.12    spl6_94 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f5577,f387,f5647])).
% 13.46/2.12  fof(f5577,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f461,f461,f312])).
% 13.46/2.12  fof(f5655,plain,(
% 13.46/2.12    spl6_93 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5654,f707,f562,f5639])).
% 13.46/2.12  fof(f5654,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5578,f709])).
% 13.46/2.12  fof(f5578,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f461,f461,f312])).
% 13.46/2.12  fof(f5653,plain,(
% 13.46/2.12    spl6_93 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f5580,f169,f5639])).
% 13.46/2.12  fof(f5580,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f461,f461,f312])).
% 13.46/2.12  fof(f5652,plain,(
% 13.46/2.12    spl6_93 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5651,f805,f5639])).
% 13.46/2.12  fof(f5651,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f5584,f1231])).
% 13.46/2.12  fof(f5584,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f461,f461,f312])).
% 13.46/2.12  fof(f5650,plain,(
% 13.46/2.12    spl6_94 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f5586,f387,f5647])).
% 13.46/2.12  fof(f5586,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f461,f461,f312])).
% 13.46/2.12  fof(f5645,plain,(
% 13.46/2.12    spl6_93 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5644,f707,f562,f5639])).
% 13.46/2.12  fof(f5644,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5587,f709])).
% 13.46/2.12  fof(f5587,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f461,f461,f312])).
% 13.46/2.12  fof(f5643,plain,(
% 13.46/2.12    spl6_93 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f5589,f169,f5639])).
% 13.46/2.12  fof(f5589,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f461,f461,f312])).
% 13.46/2.12  fof(f5642,plain,(
% 13.46/2.12    spl6_93 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5637,f805,f5639])).
% 13.46/2.12  fof(f5637,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f5593,f1231])).
% 13.46/2.12  fof(f5593,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_subset_1(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f461,f461,f312])).
% 13.46/2.12  fof(f5619,plain,(
% 13.46/2.12    spl6_92 | ~spl6_13 | ~spl6_61),
% 13.46/2.12    inference(avatar_split_clause,[],[f5614,f4093,f314,f5616])).
% 13.46/2.12  fof(f314,plain,(
% 13.46/2.12    spl6_13 <=> k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 13.46/2.12  fof(f5614,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK1,sK1,sK1) | (~spl6_13 | ~spl6_61)),
% 13.46/2.12    inference(forward_demodulation,[],[f5611,f4095])).
% 13.46/2.12  fof(f5611,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) | ~spl6_13),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f461,f453])).
% 13.46/2.12  fof(f453,plain,(
% 13.46/2.12    ( ! [X3] : (k4_subset_1(sK0,sK1,sK1) = k4_subset_1(X3,sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X3))) ) | ~spl6_13),
% 13.46/2.12    inference(duplicate_literal_removal,[],[f442])).
% 13.46/2.12  fof(f442,plain,(
% 13.46/2.12    ( ! [X3] : (k4_subset_1(sK0,sK1,sK1) = k4_subset_1(X3,sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X3)) | ~m1_subset_1(sK1,k1_zfmisc_1(X3))) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f316,f144])).
% 13.46/2.12  fof(f316,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | ~spl6_13),
% 13.46/2.12    inference(avatar_component_clause,[],[f314])).
% 13.46/2.12  fof(f5420,plain,(
% 13.46/2.12    spl6_90 | ~spl6_2),
% 13.46/2.12    inference(avatar_split_clause,[],[f5334,f140,f5409])).
% 13.46/2.12  fof(f5409,plain,(
% 13.46/2.12    spl6_90 <=> k4_subset_1(sK0,k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 13.46/2.12  fof(f5334,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) | ~spl6_2),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f142,f178,f144])).
% 13.46/2.12  fof(f5419,plain,(
% 13.46/2.12    spl6_91 | ~spl6_6 | ~spl6_8),
% 13.46/2.12    inference(avatar_split_clause,[],[f5418,f225,f193,f5414])).
% 13.46/2.12  fof(f5414,plain,(
% 13.46/2.12    spl6_91 <=> k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 13.46/2.12  fof(f5418,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.12    inference(forward_demodulation,[],[f5335,f227])).
% 13.46/2.12  fof(f5335,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k3_subset_1(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0)) | ~spl6_6),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f195,f178,f144])).
% 13.46/2.12  fof(f5417,plain,(
% 13.46/2.12    spl6_91 | ~spl6_22),
% 13.46/2.12    inference(avatar_split_clause,[],[f5336,f435,f5414])).
% 13.46/2.12  fof(f5336,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) | ~spl6_22),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f178,f144])).
% 13.46/2.12  fof(f5412,plain,(
% 13.46/2.12    spl6_90 | ~spl6_21 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5407,f707,f427,f5409])).
% 13.46/2.12  fof(f5407,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5337,f709])).
% 13.46/2.12  fof(f5337,plain,(
% 13.46/2.12    k4_subset_1(sK0,k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f178,f144])).
% 13.46/2.12  fof(f5405,plain,(
% 13.46/2.12    spl6_88 | ~spl6_2),
% 13.46/2.12    inference(avatar_split_clause,[],[f5404,f140,f5388])).
% 13.46/2.12  fof(f5404,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK0,sK1,k1_xboole_0) | ~spl6_2),
% 13.46/2.12    inference(forward_demodulation,[],[f5403,f64])).
% 13.46/2.12  fof(f5403,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) | ~spl6_2),
% 13.46/2.12    inference(forward_demodulation,[],[f5339,f499])).
% 13.46/2.12  fof(f5339,plain,(
% 13.46/2.12    k4_subset_1(sK0,sK1,k1_xboole_0) = k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) | ~spl6_2),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f142,f178,f144])).
% 13.46/2.12  fof(f5402,plain,(
% 13.46/2.12    spl6_89 | ~spl6_6 | ~spl6_8),
% 13.46/2.12    inference(avatar_split_clause,[],[f5401,f225,f193,f5395])).
% 13.46/2.12  fof(f5401,plain,(
% 13.46/2.12    k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl6_6 | ~spl6_8)),
% 13.46/2.12    inference(forward_demodulation,[],[f5400,f227])).
% 13.46/2.12  fof(f5400,plain,(
% 13.46/2.12    k3_subset_1(sK0,sK1) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) | ~spl6_6),
% 13.46/2.12    inference(forward_demodulation,[],[f5399,f64])).
% 13.46/2.12  fof(f5399,plain,(
% 13.46/2.12    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k5_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0) | ~spl6_6),
% 13.46/2.12    inference(forward_demodulation,[],[f5340,f499])).
% 13.46/2.12  fof(f5340,plain,(
% 13.46/2.12    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k1_xboole_0) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k1_xboole_0,k3_subset_1(sK0,sK1))) | ~spl6_6),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f195,f178,f144])).
% 13.46/2.12  fof(f5398,plain,(
% 13.46/2.12    spl6_89 | ~spl6_22),
% 13.46/2.12    inference(avatar_split_clause,[],[f5393,f435,f5395])).
% 13.46/2.12  fof(f5393,plain,(
% 13.46/2.12    k4_xboole_0(sK0,sK1) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_22),
% 13.46/2.12    inference(forward_demodulation,[],[f5392,f64])).
% 13.46/2.12  fof(f5392,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_22),
% 13.46/2.12    inference(forward_demodulation,[],[f5341,f499])).
% 13.46/2.12  fof(f5341,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl6_22),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f178,f144])).
% 13.46/2.12  fof(f5391,plain,(
% 13.46/2.12    spl6_88 | ~spl6_21 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5386,f707,f427,f5388])).
% 13.46/2.12  fof(f5386,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK0,sK1,k1_xboole_0) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f5385,f709])).
% 13.46/2.12  fof(f5385,plain,(
% 13.46/2.12    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl6_21),
% 13.46/2.12    inference(forward_demodulation,[],[f5384,f64])).
% 13.46/2.12  fof(f5384,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl6_21),
% 13.46/2.12    inference(forward_demodulation,[],[f5342,f499])).
% 13.46/2.12  fof(f5342,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f178,f144])).
% 13.46/2.12  fof(f5320,plain,(
% 13.46/2.12    spl6_87 | ~spl6_51 | ~spl6_71),
% 13.46/2.12    inference(avatar_split_clause,[],[f5315,f5058,f3948,f5317])).
% 13.46/2.12  fof(f5317,plain,(
% 13.46/2.12    spl6_87 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 13.46/2.12  fof(f3948,plain,(
% 13.46/2.12    spl6_51 <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1)),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 13.46/2.12  fof(f5315,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl6_51 | ~spl6_71)),
% 13.46/2.12    inference(forward_demodulation,[],[f3950,f5060])).
% 13.46/2.12  fof(f3950,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1) | ~spl6_51),
% 13.46/2.12    inference(avatar_component_clause,[],[f3948])).
% 13.46/2.12  fof(f5275,plain,(
% 13.46/2.12    spl6_86 | ~spl6_15),
% 13.46/2.12    inference(avatar_split_clause,[],[f4665,f387,f5272])).
% 13.46/2.12  fof(f5272,plain,(
% 13.46/2.12    spl6_86 <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 13.46/2.12  fof(f4665,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_15),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f389,f507,f131])).
% 13.46/2.12  fof(f5270,plain,(
% 13.46/2.12    spl6_85 | ~spl6_24 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f5269,f707,f562,f5264])).
% 13.46/2.12  fof(f5264,plain,(
% 13.46/2.12    spl6_85 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 13.46/2.12  fof(f5269,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) | (~spl6_24 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f4666,f709])).
% 13.46/2.12  fof(f4666,plain,(
% 13.46/2.12    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_24),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f564,f507,f131])).
% 13.46/2.12  fof(f5268,plain,(
% 13.46/2.12    spl6_85 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f4668,f169,f5264])).
% 13.46/2.12  fof(f4668,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f131])).
% 13.46/2.12  fof(f5267,plain,(
% 13.46/2.12    spl6_85 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5262,f805,f5264])).
% 13.46/2.12  fof(f5262,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k1_xboole_0)) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f4672,f1231])).
% 13.46/2.12  fof(f4672,plain,(
% 13.46/2.12    r2_hidden(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0)) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f131])).
% 13.46/2.12  fof(f5251,plain,(
% 13.46/2.12    ~spl6_84 | spl6_14),
% 13.46/2.12    inference(avatar_split_clause,[],[f4681,f329,f5248])).
% 13.46/2.12  fof(f5248,plain,(
% 13.46/2.12    spl6_84 <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(sK1),k1_xboole_0)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 13.46/2.12  fof(f4681,plain,(
% 13.46/2.12    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_zfmisc_1(sK1),k1_xboole_0))) | spl6_14),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f331,f507,f150])).
% 13.46/2.12  fof(f5229,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4779,f209,f5058])).
% 13.46/2.12  fof(f4779,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f78])).
% 13.46/2.12  fof(f5228,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4781,f209,f5058])).
% 13.46/2.12  fof(f4781,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f78])).
% 13.46/2.12  fof(f5227,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5226,f209,f5058])).
% 13.46/2.12  fof(f5226,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4783,f499])).
% 13.46/2.12  fof(f4783,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,sK0)) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f260])).
% 13.46/2.12  fof(f260,plain,(
% 13.46/2.12    ( ! [X4,X2,X3] : (r2_hidden(sK2(X2,k4_xboole_0(X3,X4)),X3) | r2_hidden(sK2(X2,k4_xboole_0(X3,X4)),X2) | k4_xboole_0(X3,X4) = X2) )),
% 13.46/2.12    inference(resolution,[],[f78,f133])).
% 13.46/2.12  fof(f5224,plain,(
% 13.46/2.12    spl6_73 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5223,f209,f5073])).
% 13.46/2.12  fof(f5073,plain,(
% 13.46/2.12    spl6_73 <=> k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 13.46/2.12  fof(f5223,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4788,f499])).
% 13.46/2.12  fof(f4788,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f288])).
% 13.46/2.12  fof(f288,plain,(
% 13.46/2.12    ( ! [X6,X8,X7] : (r2_hidden(sK2(X6,k5_xboole_0(X7,k4_xboole_0(X8,X7))),X8) | r2_hidden(sK2(X6,k5_xboole_0(X7,k4_xboole_0(X8,X7))),X7) | k5_xboole_0(X7,k4_xboole_0(X8,X7)) = X6 | r2_hidden(sK2(X6,k5_xboole_0(X7,k4_xboole_0(X8,X7))),X6)) )),
% 13.46/2.12    inference(resolution,[],[f150,f78])).
% 13.46/2.12  fof(f5222,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5221,f209,f5058])).
% 13.46/2.12  fof(f5221,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4789,f526])).
% 13.46/2.12  fof(f4789,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f288])).
% 13.46/2.12  fof(f5220,plain,(
% 13.46/2.12    spl6_72 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5219,f209,f5065])).
% 13.46/2.12  fof(f5065,plain,(
% 13.46/2.12    spl6_72 <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 13.46/2.12  fof(f5219,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4791,f1044])).
% 13.46/2.12  fof(f1044,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(sK1,sK0) = k4_xboole_0(k4_xboole_0(sK1,sK0),X0)) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f300])).
% 13.46/2.12  fof(f300,plain,(
% 13.46/2.12    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 13.46/2.12    inference(factoring,[],[f99])).
% 13.46/2.12  fof(f4791,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f507,f288])).
% 13.46/2.12  fof(f5218,plain,(
% 13.46/2.12    spl6_70 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5217,f209,f5051])).
% 13.46/2.12  fof(f5051,plain,(
% 13.46/2.12    spl6_70 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 13.46/2.12  fof(f5217,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4792,f1044])).
% 13.46/2.12  fof(f4792,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f288])).
% 13.46/2.12  fof(f5216,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5215,f209,f5058])).
% 13.46/2.12  fof(f5215,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4793,f526])).
% 13.46/2.12  fof(f4793,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f288])).
% 13.46/2.12  fof(f5214,plain,(
% 13.46/2.12    spl6_74 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5213,f209,f5083])).
% 13.46/2.12  fof(f5083,plain,(
% 13.46/2.12    spl6_74 <=> k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 13.46/2.12  fof(f5213,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4795,f1044])).
% 13.46/2.12  fof(f4795,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f507,f288])).
% 13.46/2.12  fof(f5212,plain,(
% 13.46/2.12    spl6_73 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5211,f209,f5073])).
% 13.46/2.12  fof(f5211,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4796,f499])).
% 13.46/2.12  fof(f4796,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f288])).
% 13.46/2.12  fof(f5210,plain,(
% 13.46/2.12    spl6_70 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5209,f209,f5051])).
% 13.46/2.12  fof(f5209,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4797,f1044])).
% 13.46/2.12  fof(f4797,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f288])).
% 13.46/2.12  fof(f5207,plain,(
% 13.46/2.12    spl6_73 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5206,f209,f5073])).
% 13.46/2.12  fof(f5206,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4800,f499])).
% 13.46/2.12  fof(f4800,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f147])).
% 13.46/2.12  fof(f5205,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5204,f209,f5058])).
% 13.46/2.12  fof(f5204,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4801,f526])).
% 13.46/2.12  fof(f4801,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f147])).
% 13.46/2.12  fof(f5203,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4804,f209,f5058])).
% 13.46/2.12  fof(f4804,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f542,f542,f507,f507,f351])).
% 13.46/2.12  fof(f5202,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4805,f209,f5058])).
% 13.46/2.12  fof(f4805,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).
% 13.46/2.12  fof(f5201,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4808,f209,f5058])).
% 13.46/2.12  fof(f4808,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f507,f542,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5200,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4809,f209,f5058])).
% 13.46/2.12  fof(f4809,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5199,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4812,f209,f5058])).
% 13.46/2.12  fof(f4812,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5198,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4814,f209,f5058])).
% 13.46/2.12  fof(f4814,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f507,f507,f507,f542,f507,f351])).
% 13.46/2.12  fof(f5197,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4815,f209,f5058])).
% 13.46/2.12  fof(f4815,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).
% 13.46/2.12  fof(f5196,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4817,f209,f5058])).
% 13.46/2.12  fof(f4817,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5195,plain,(
% 13.46/2.12    spl6_83 | ~spl6_4 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4827,f209,f169,f5191])).
% 13.46/2.12  fof(f5191,plain,(
% 13.46/2.12    spl6_83 <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 13.46/2.12  fof(f4827,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f542,f542,f507,f359])).
% 13.46/2.12  fof(f359,plain,(
% 13.46/2.12    ( ! [X19,X17,X18,X16] : (r2_hidden(sK4(X16,X17,X18),X18) | ~r2_hidden(X19,X16) | r2_hidden(sK4(X16,X17,X18),X17) | r2_hidden(sK4(X16,X17,X18),X16) | r2_hidden(X19,X18)) )),
% 13.46/2.12    inference(superposition,[],[f149,f147])).
% 13.46/2.12  fof(f5194,plain,(
% 13.46/2.12    spl6_83 | ~spl6_7 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5189,f805,f209,f5191])).
% 13.46/2.12  fof(f5189,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(forward_demodulation,[],[f4831,f1231])).
% 13.46/2.12  fof(f4831,plain,(
% 13.46/2.12    r2_hidden(sK4(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f542,f542,f507,f359])).
% 13.46/2.12  fof(f5187,plain,(
% 13.46/2.12    spl6_82 | ~spl6_4 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4849,f209,f169,f5183])).
% 13.46/2.12  fof(f5183,plain,(
% 13.46/2.12    spl6_82 <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 13.46/2.12  fof(f4849,plain,(
% 13.46/2.12    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f542,f542,f507,f360])).
% 13.46/2.12  fof(f360,plain,(
% 13.46/2.12    ( ! [X23,X21,X22,X20] : (r2_hidden(sK4(X20,X21,X22),X22) | r2_hidden(X23,X21) | r2_hidden(X23,X20) | r2_hidden(sK4(X20,X21,X22),X21) | r2_hidden(sK4(X20,X21,X22),X20) | ~r2_hidden(X23,X22)) )),
% 13.46/2.12    inference(superposition,[],[f150,f147])).
% 13.46/2.12  fof(f5186,plain,(
% 13.46/2.12    spl6_82 | ~spl6_7 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5181,f805,f209,f5183])).
% 13.46/2.12  fof(f5181,plain,(
% 13.46/2.12    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(forward_demodulation,[],[f4853,f1231])).
% 13.46/2.12  fof(f4853,plain,(
% 13.46/2.12    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f542,f542,f507,f360])).
% 13.46/2.12  fof(f5179,plain,(
% 13.46/2.12    spl6_72 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5178,f209,f5065])).
% 13.46/2.12  fof(f5178,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4867,f1044])).
% 13.46/2.12  fof(f4867,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f507,f147])).
% 13.46/2.12  fof(f5177,plain,(
% 13.46/2.12    spl6_70 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5176,f209,f5051])).
% 13.46/2.12  fof(f5176,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4868,f1044])).
% 13.46/2.12  fof(f4868,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f147])).
% 13.46/2.12  fof(f5175,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5174,f209,f5058])).
% 13.46/2.12  fof(f5174,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4869,f526])).
% 13.46/2.12  fof(f4869,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f147])).
% 13.46/2.12  fof(f5173,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4872,f209,f5058])).
% 13.46/2.12  fof(f4872,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5172,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4873,f209,f5058])).
% 13.46/2.12  fof(f4873,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5171,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4876,f209,f5058])).
% 13.46/2.12  fof(f4876,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5170,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4877,f209,f5058])).
% 13.46/2.12  fof(f4877,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5169,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4880,f209,f5058])).
% 13.46/2.12  fof(f4880,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f507,f542,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5168,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4881,f209,f5058])).
% 13.46/2.12  fof(f4881,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5167,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4884,f209,f5058])).
% 13.46/2.12  fof(f4884,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f507,f507,f542,f507,f507,f351])).
% 13.46/2.12  fof(f5166,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4885,f209,f5058])).
% 13.46/2.12  fof(f4885,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5165,plain,(
% 13.46/2.12    spl6_81 | ~spl6_4 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4891,f209,f169,f5161])).
% 13.46/2.12  fof(f5161,plain,(
% 13.46/2.12    spl6_81 <=> r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 13.46/2.12  fof(f4891,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f542,f542,f507,f358])).
% 13.46/2.12  fof(f358,plain,(
% 13.46/2.12    ( ! [X14,X12,X15,X13] : (r2_hidden(sK4(X12,X13,X14),X14) | ~r2_hidden(X15,X13) | r2_hidden(sK4(X12,X13,X14),X13) | r2_hidden(sK4(X12,X13,X14),X12) | r2_hidden(X15,X14)) )),
% 13.46/2.12    inference(superposition,[],[f148,f147])).
% 13.46/2.12  fof(f5164,plain,(
% 13.46/2.12    spl6_81 | ~spl6_7 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5159,f805,f209,f5161])).
% 13.46/2.12  fof(f5159,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(forward_demodulation,[],[f4895,f1231])).
% 13.46/2.12  fof(f4895,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k4_xboole_0(sK1,sK0)),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f542,f542,f507,f358])).
% 13.46/2.12  fof(f5157,plain,(
% 13.46/2.12    spl6_80 | ~spl6_4 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4917,f209,f169,f5153])).
% 13.46/2.12  fof(f5153,plain,(
% 13.46/2.12    spl6_80 <=> r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 13.46/2.12  fof(f4917,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f542,f542,f507,f360])).
% 13.46/2.12  fof(f5156,plain,(
% 13.46/2.12    spl6_80 | ~spl6_7 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5151,f805,f209,f5153])).
% 13.46/2.12  fof(f5151,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(forward_demodulation,[],[f4921,f1231])).
% 13.46/2.12  fof(f4921,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK1,sK0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f542,f542,f507,f360])).
% 13.46/2.12  fof(f5150,plain,(
% 13.46/2.12    spl6_79 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f4928,f169,f5146])).
% 13.46/2.12  fof(f5146,plain,(
% 13.46/2.12    spl6_79 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 13.46/2.12  fof(f4928,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f507,f507,f507,f360])).
% 13.46/2.12  fof(f5149,plain,(
% 13.46/2.12    spl6_79 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5144,f805,f5146])).
% 13.46/2.12  fof(f5144,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f4932,f1231])).
% 13.46/2.12  fof(f4932,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f507,f507,f507,f360])).
% 13.46/2.12  fof(f5143,plain,(
% 13.46/2.12    spl6_74 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5142,f209,f5083])).
% 13.46/2.12  fof(f5142,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4935,f1044])).
% 13.46/2.12  fof(f4935,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f507,f147])).
% 13.46/2.12  fof(f5141,plain,(
% 13.46/2.12    spl6_73 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5140,f209,f5073])).
% 13.46/2.12  fof(f5140,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4936,f499])).
% 13.46/2.12  fof(f4936,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f147])).
% 13.46/2.12  fof(f5139,plain,(
% 13.46/2.12    spl6_70 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5138,f209,f5051])).
% 13.46/2.12  fof(f5138,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f4937,f1044])).
% 13.46/2.12  fof(f4937,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f147])).
% 13.46/2.12  fof(f5137,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4939,f209,f5058])).
% 13.46/2.12  fof(f4939,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f542,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5136,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4941,f209,f5058])).
% 13.46/2.12  fof(f4941,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5135,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4943,f209,f5058])).
% 13.46/2.12  fof(f4943,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).
% 13.46/2.12  fof(f5134,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4945,f209,f5058])).
% 13.46/2.12  fof(f4945,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5133,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4947,f209,f5058])).
% 13.46/2.12  fof(f4947,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f542,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5132,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4949,f209,f5058])).
% 13.46/2.12  fof(f4949,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f542,f542,f507,f351])).
% 13.46/2.12  fof(f5131,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4951,f209,f5058])).
% 13.46/2.12  fof(f4951,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f542,f542,f507,f507,f351])).
% 13.46/2.12  fof(f5130,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4953,f209,f5058])).
% 13.46/2.12  fof(f4953,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f507,f507,f507,f351])).
% 13.46/2.12  fof(f5129,plain,(
% 13.46/2.12    spl6_78 | ~spl6_4 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4959,f209,f169,f5125])).
% 13.46/2.12  fof(f5125,plain,(
% 13.46/2.12    spl6_78 <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 13.46/2.12  fof(f4959,plain,(
% 13.46/2.12    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f542,f507,f358])).
% 13.46/2.12  fof(f5128,plain,(
% 13.46/2.12    spl6_78 | ~spl6_7 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5123,f805,f209,f5125])).
% 13.46/2.12  fof(f5123,plain,(
% 13.46/2.12    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(forward_demodulation,[],[f4963,f1231])).
% 13.46/2.12  fof(f4963,plain,(
% 13.46/2.12    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f542,f507,f358])).
% 13.46/2.12  fof(f5122,plain,(
% 13.46/2.12    spl6_77 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f4968,f169,f5118])).
% 13.46/2.12  fof(f5118,plain,(
% 13.46/2.12    spl6_77 <=> r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 13.46/2.12  fof(f4968,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0)) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f507,f507,f358])).
% 13.46/2.12  fof(f5121,plain,(
% 13.46/2.12    spl6_77 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5116,f805,f5118])).
% 13.46/2.12  fof(f5116,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k1_zfmisc_1(sK0),k1_xboole_0),k1_zfmisc_1(sK0)) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f4972,f1231])).
% 13.46/2.12  fof(f4972,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f507,f507,f358])).
% 13.46/2.12  fof(f5115,plain,(
% 13.46/2.12    spl6_76 | ~spl6_4 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f4981,f209,f169,f5111])).
% 13.46/2.12  fof(f5111,plain,(
% 13.46/2.12    spl6_76 <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k1_xboole_0),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 13.46/2.12  fof(f4981,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k1_xboole_0),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f542,f507,f359])).
% 13.46/2.12  fof(f5114,plain,(
% 13.46/2.12    spl6_76 | ~spl6_7 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5109,f805,f209,f5111])).
% 13.46/2.12  fof(f5109,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k1_xboole_0),k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(forward_demodulation,[],[f4985,f1231])).
% 13.46/2.12  fof(f4985,plain,(
% 13.46/2.12    r2_hidden(sK4(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k4_xboole_0(sK1,sK0),k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | (~spl6_7 | ~spl6_29)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f542,f507,f359])).
% 13.46/2.12  fof(f5108,plain,(
% 13.46/2.12    spl6_75 | ~spl6_4),
% 13.46/2.12    inference(avatar_split_clause,[],[f4992,f169,f5104])).
% 13.46/2.12  fof(f5104,plain,(
% 13.46/2.12    spl6_75 <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 13.46/2.12  fof(f4992,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0)) | ~spl6_4),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f171,f507,f507,f507,f359])).
% 13.46/2.12  fof(f5107,plain,(
% 13.46/2.12    spl6_75 | ~spl6_29),
% 13.46/2.12    inference(avatar_split_clause,[],[f5102,f805,f5104])).
% 13.46/2.12  fof(f5102,plain,(
% 13.46/2.12    r2_hidden(sK4(k1_zfmisc_1(sK0),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0)) | ~spl6_29),
% 13.46/2.12    inference(forward_demodulation,[],[f4996,f1231])).
% 13.46/2.12  fof(f4996,plain,(
% 13.46/2.12    r2_hidden(sK4(k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)),k1_xboole_0,k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | ~spl6_29),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f807,f507,f507,f507,f359])).
% 13.46/2.12  fof(f5101,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5100,f209,f5058])).
% 13.46/2.12  fof(f5100,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5006,f499])).
% 13.46/2.12  fof(f5006,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,sK0)) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f99])).
% 13.46/2.12  fof(f5093,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5092,f209,f5058])).
% 13.46/2.12  fof(f5092,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5091,f526])).
% 13.46/2.12  fof(f5091,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5013,f1044])).
% 13.46/2.12  fof(f5013,plain,(
% 13.46/2.12    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK1,sK0),X0)) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f299])).
% 13.46/2.12  fof(f5090,plain,(
% 13.46/2.12    spl6_73 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5089,f209,f5073])).
% 13.46/2.12  fof(f5089,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5088,f499])).
% 13.46/2.12  fof(f5088,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) ) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5014,f499])).
% 13.46/2.12  fof(f5014,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f299])).
% 13.46/2.12  fof(f5086,plain,(
% 13.46/2.12    spl6_74 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5081,f209,f5083])).
% 13.46/2.12  fof(f5081,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5080,f499])).
% 13.46/2.12  fof(f5080,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))) ) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5016,f1044])).
% 13.46/2.12  fof(f5016,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)))) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f507,f299])).
% 13.46/2.12  fof(f5079,plain,(
% 13.46/2.12    spl6_70 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5078,f209,f5051])).
% 13.46/2.12  fof(f5078,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5077,f499])).
% 13.46/2.12  fof(f5077,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) ) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5017,f1044])).
% 13.46/2.12  fof(f5017,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f299])).
% 13.46/2.12  fof(f5076,plain,(
% 13.46/2.12    spl6_73 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5071,f209,f5073])).
% 13.46/2.12  fof(f5071,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5070,f499])).
% 13.46/2.12  fof(f5070,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)) ) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5018,f499])).
% 13.46/2.12  fof(f5018,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)))) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f299])).
% 13.46/2.12  fof(f5068,plain,(
% 13.46/2.12    spl6_72 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5063,f209,f5065])).
% 13.46/2.12  fof(f5063,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5062,f1044])).
% 13.46/2.12  fof(f5062,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK0),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) ) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5020,f1044])).
% 13.46/2.12  fof(f5020,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK1,sK0),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f542,f507,f299])).
% 13.46/2.12  fof(f5061,plain,(
% 13.46/2.12    spl6_71 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5056,f209,f5058])).
% 13.46/2.12  fof(f5056,plain,(
% 13.46/2.12    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5055,f526])).
% 13.46/2.12  fof(f5055,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5021,f1044])).
% 13.46/2.12  fof(f5021,plain,(
% 13.46/2.12    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK1,sK0),X0)) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f507,f542,f507,f299])).
% 13.46/2.12  fof(f5054,plain,(
% 13.46/2.12    spl6_70 | ~spl6_7),
% 13.46/2.12    inference(avatar_split_clause,[],[f5049,f209,f5051])).
% 13.46/2.12  fof(f5049,plain,(
% 13.46/2.12    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5048,f499])).
% 13.46/2.12  fof(f5048,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))) ) | ~spl6_7),
% 13.46/2.12    inference(forward_demodulation,[],[f5022,f1044])).
% 13.46/2.12  fof(f5022,plain,(
% 13.46/2.12    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0))) ) | ~spl6_7),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f542,f507,f507,f299])).
% 13.46/2.12  fof(f4642,plain,(
% 13.46/2.12    ~spl6_69 | spl6_63),
% 13.46/2.12    inference(avatar_split_clause,[],[f4637,f4120,f4639])).
% 13.46/2.12  fof(f4639,plain,(
% 13.46/2.12    spl6_69 <=> r2_hidden(sK0,k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 13.46/2.12  fof(f4120,plain,(
% 13.46/2.12    spl6_63 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 13.46/2.12  fof(f4637,plain,(
% 13.46/2.12    ~r2_hidden(sK0,k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | spl6_63),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f4122,f127])).
% 13.46/2.12  fof(f4122,plain,(
% 13.46/2.12    ~r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | spl6_63),
% 13.46/2.12    inference(avatar_component_clause,[],[f4120])).
% 13.46/2.12  fof(f4531,plain,(
% 13.46/2.12    ~spl6_67 | spl6_68 | ~spl6_20 | ~spl6_62),
% 13.46/2.12    inference(avatar_split_clause,[],[f4522,f4100,f419,f4528,f4524])).
% 13.46/2.12  fof(f4522,plain,(
% 13.46/2.12    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1)) | ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | (~spl6_20 | ~spl6_62)),
% 13.46/2.12    inference(forward_demodulation,[],[f4521,f4102])).
% 13.46/2.12  fof(f4521,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK1)) | ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl6_20),
% 13.46/2.12    inference(forward_demodulation,[],[f4503,f525])).
% 13.46/2.12  fof(f4503,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) | ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl6_20),
% 13.46/2.12    inference(superposition,[],[f421,f235])).
% 13.46/2.12  fof(f4426,plain,(
% 13.46/2.12    spl6_47),
% 13.46/2.12    inference(avatar_contradiction_clause,[],[f4422])).
% 13.46/2.12  fof(f4422,plain,(
% 13.46/2.12    $false | spl6_47),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f161,f3930,f127])).
% 13.46/2.12  fof(f3930,plain,(
% 13.46/2.12    ~r1_tarski(sK1,sK1) | spl6_47),
% 13.46/2.12    inference(avatar_component_clause,[],[f3928])).
% 13.46/2.12  fof(f4425,plain,(
% 13.46/2.12    spl6_47),
% 13.46/2.12    inference(avatar_contradiction_clause,[],[f4420])).
% 13.46/2.12  fof(f4420,plain,(
% 13.46/2.12    $false | spl6_47),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f124,f3930])).
% 13.46/2.12  fof(f4424,plain,(
% 13.46/2.12    spl6_47),
% 13.46/2.12    inference(avatar_contradiction_clause,[],[f4423])).
% 13.46/2.12  fof(f4423,plain,(
% 13.46/2.12    $false | spl6_47),
% 13.46/2.12    inference(resolution,[],[f3930,f124])).
% 13.46/2.12  fof(f4356,plain,(
% 13.46/2.12    ~spl6_2 | spl6_66 | ~spl6_13),
% 13.46/2.12    inference(avatar_split_clause,[],[f4278,f314,f4353,f140])).
% 13.46/2.12  fof(f4353,plain,(
% 13.46/2.12    spl6_66 <=> ! [X1,X0] : (~r2_hidden(X1,k4_subset_1(X0,sK1,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r2_hidden(X1,sK1))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 13.46/2.12  fof(f4278,plain,(
% 13.46/2.12    ( ! [X2,X3] : (~r2_hidden(X3,k4_subset_1(X2,sK1,sK1)) | r2_hidden(X3,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | ~spl6_13),
% 13.46/2.12    inference(duplicate_literal_removal,[],[f4277])).
% 13.46/2.12  fof(f4277,plain,(
% 13.46/2.12    ( ! [X2,X3] : (~r2_hidden(X3,k4_subset_1(X2,sK1,sK1)) | r2_hidden(X3,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f450,f309])).
% 13.46/2.12  fof(f450,plain,(
% 13.46/2.12    ( ! [X6] : (~r2_hidden(X6,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X6,sK1)) ) | ~spl6_13),
% 13.46/2.12    inference(duplicate_literal_removal,[],[f449])).
% 13.46/2.12  fof(f449,plain,(
% 13.46/2.12    ( ! [X6] : (~r2_hidden(X6,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X6,sK1) | r2_hidden(X6,sK1)) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f150,f316])).
% 13.46/2.12  fof(f4355,plain,(
% 13.46/2.12    ~spl6_2 | spl6_66 | ~spl6_13),
% 13.46/2.12    inference(avatar_split_clause,[],[f4279,f314,f4353,f140])).
% 13.46/2.12  fof(f4279,plain,(
% 13.46/2.12    ( ! [X0,X1] : (~r2_hidden(X1,k4_subset_1(X0,sK1,sK1)) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl6_13),
% 13.46/2.12    inference(duplicate_literal_removal,[],[f4276])).
% 13.46/2.12  fof(f4276,plain,(
% 13.46/2.12    ( ! [X0,X1] : (~r2_hidden(X1,k4_subset_1(X0,sK1,sK1)) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f450,f309])).
% 13.46/2.12  fof(f4249,plain,(
% 13.46/2.12    ~spl6_2 | spl6_65 | ~spl6_13),
% 13.46/2.12    inference(avatar_split_clause,[],[f4193,f314,f4246,f140])).
% 13.46/2.12  fof(f4246,plain,(
% 13.46/2.12    spl6_65 <=> ! [X1,X0] : (r2_hidden(X1,k4_subset_1(X0,sK1,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~r2_hidden(X1,sK1))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 13.46/2.12  fof(f4193,plain,(
% 13.46/2.12    ( ! [X2,X3] : (r2_hidden(X3,k4_subset_1(X2,sK1,sK1)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | ~spl6_13),
% 13.46/2.12    inference(duplicate_literal_removal,[],[f4192])).
% 13.46/2.12  fof(f4192,plain,(
% 13.46/2.12    ( ! [X2,X3] : (r2_hidden(X3,k4_subset_1(X2,sK1,sK1)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f447,f309])).
% 13.46/2.12  fof(f447,plain,(
% 13.46/2.12    ( ! [X4] : (r2_hidden(X4,k4_subset_1(sK0,sK1,sK1)) | ~r2_hidden(X4,sK1)) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f148,f316])).
% 13.46/2.12  fof(f4248,plain,(
% 13.46/2.12    ~spl6_2 | spl6_65 | ~spl6_13),
% 13.46/2.12    inference(avatar_split_clause,[],[f4194,f314,f4246,f140])).
% 13.46/2.12  fof(f4194,plain,(
% 13.46/2.12    ( ! [X0,X1] : (r2_hidden(X1,k4_subset_1(X0,sK1,sK1)) | ~r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl6_13),
% 13.46/2.12    inference(duplicate_literal_removal,[],[f4191])).
% 13.46/2.12  fof(f4191,plain,(
% 13.46/2.12    ( ! [X0,X1] : (r2_hidden(X1,k4_subset_1(X0,sK1,sK1)) | ~r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl6_13),
% 13.46/2.12    inference(superposition,[],[f447,f309])).
% 13.46/2.12  fof(f4127,plain,(
% 13.46/2.12    ~spl6_63 | spl6_64 | ~spl6_21),
% 13.46/2.12    inference(avatar_split_clause,[],[f4118,f427,f4124,f4120])).
% 13.46/2.12  fof(f4124,plain,(
% 13.46/2.12    spl6_64 <=> m1_subset_1(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 13.46/2.12  fof(f4118,plain,(
% 13.46/2.12    m1_subset_1(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0)) | ~r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_21),
% 13.46/2.12    inference(forward_demodulation,[],[f4086,f525])).
% 13.46/2.12  fof(f4086,plain,(
% 13.46/2.12    m1_subset_1(k5_xboole_0(sK0,sK0),k1_zfmisc_1(sK0)) | ~r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_21),
% 13.46/2.12    inference(superposition,[],[f429,f235])).
% 13.46/2.12  fof(f4111,plain,(
% 13.46/2.12    spl6_61 | ~spl6_21 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f4110,f707,f427,f4093])).
% 13.46/2.12  fof(f4110,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK0,sK1,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f4109,f709])).
% 13.46/2.12  fof(f4109,plain,(
% 13.46/2.12    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.12    inference(forward_demodulation,[],[f4058,f526])).
% 13.46/2.12  fof(f4058,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f429,f144])).
% 13.46/2.12  fof(f4107,plain,(
% 13.46/2.12    spl6_62 | ~spl6_6 | ~spl6_8 | ~spl6_21 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f4106,f707,f427,f225,f193,f4100])).
% 13.46/2.12  fof(f4106,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) | (~spl6_6 | ~spl6_8 | ~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f4105,f709])).
% 13.46/2.12  fof(f4105,plain,(
% 13.46/2.12    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_21)),
% 13.46/2.12    inference(forward_demodulation,[],[f4104,f370])).
% 13.46/2.12  fof(f370,plain,(
% 13.46/2.12    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,X5)) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X5)),k4_xboole_0(X3,X4)))) )),
% 13.46/2.12    inference(superposition,[],[f116,f114])).
% 13.46/2.12  fof(f4104,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) | (~spl6_6 | ~spl6_8 | ~spl6_21)),
% 13.46/2.12    inference(forward_demodulation,[],[f4060,f227])).
% 13.46/2.12  fof(f4060,plain,(
% 13.46/2.12    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1))) | (~spl6_6 | ~spl6_21)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f195,f429,f144])).
% 13.46/2.12  fof(f4103,plain,(
% 13.46/2.12    spl6_62 | ~spl6_21 | ~spl6_22 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f4098,f707,f435,f427,f4100])).
% 13.46/2.12  fof(f4098,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) | (~spl6_21 | ~spl6_22 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f4097,f709])).
% 13.46/2.12  fof(f4097,plain,(
% 13.46/2.12    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl6_21 | ~spl6_22)),
% 13.46/2.12    inference(forward_demodulation,[],[f4061,f370])).
% 13.46/2.12  fof(f4061,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) | (~spl6_21 | ~spl6_22)),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f437,f429,f144])).
% 13.46/2.12  fof(f4096,plain,(
% 13.46/2.12    spl6_61 | ~spl6_21 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f4091,f707,f427,f4093])).
% 13.46/2.12  fof(f4091,plain,(
% 13.46/2.12    sK1 = k4_subset_1(sK0,sK1,sK1) | (~spl6_21 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f4090,f709])).
% 13.46/2.12  fof(f4090,plain,(
% 13.46/2.12    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_21),
% 13.46/2.12    inference(forward_demodulation,[],[f4062,f526])).
% 13.46/2.12  fof(f4062,plain,(
% 13.46/2.12    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl6_21),
% 13.46/2.12    inference(unit_resulting_resolution,[],[f429,f429,f144])).
% 13.46/2.12  fof(f4050,plain,(
% 13.46/2.12    spl6_59 | spl6_60 | ~spl6_7 | ~spl6_10 | ~spl6_28),
% 13.46/2.12    inference(avatar_split_clause,[],[f4042,f707,f273,f209,f4047,f4044])).
% 13.46/2.12  fof(f4044,plain,(
% 13.46/2.12    spl6_59 <=> ! [X88] : ~r1_tarski(sK1,X88)),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 13.46/2.12  fof(f4047,plain,(
% 13.46/2.12    spl6_60 <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 13.46/2.12  fof(f273,plain,(
% 13.46/2.12    spl6_10 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 13.46/2.12  fof(f4042,plain,(
% 13.46/2.12    ( ! [X88] : (sK1 = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1)) | ~r1_tarski(sK1,X88)) ) | (~spl6_7 | ~spl6_10 | ~spl6_28)),
% 13.46/2.12    inference(forward_demodulation,[],[f4041,f709])).
% 13.46/2.12  fof(f4041,plain,(
% 13.46/2.12    ( ! [X88] : (k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1)) | ~r1_tarski(sK1,X88)) ) | (~spl6_7 | ~spl6_10)),
% 13.46/2.12    inference(forward_demodulation,[],[f4040,f113])).
% 13.46/2.12  fof(f4040,plain,(
% 13.46/2.12    ( ! [X88] : (k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1)) | ~r1_tarski(sK1,X88)) ) | (~spl6_7 | ~spl6_10)),
% 13.46/2.12    inference(forward_demodulation,[],[f3895,f1044])).
% 13.46/2.12  fof(f3895,plain,(
% 13.46/2.12    ( ! [X88] : (k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,X88))) | ~r1_tarski(sK1,X88)) ) | ~spl6_10),
% 13.46/2.12    inference(superposition,[],[f373,f275])).
% 13.46/2.12  fof(f275,plain,(
% 13.46/2.12    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.12    inference(avatar_component_clause,[],[f273])).
% 13.46/2.12  fof(f4034,plain,(
% 13.46/2.12    spl6_58 | ~spl6_7 | ~spl6_10),
% 13.46/2.12    inference(avatar_split_clause,[],[f4029,f273,f209,f4031])).
% 13.46/2.12  fof(f4031,plain,(
% 13.46/2.12    spl6_58 <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 13.46/2.12  fof(f4029,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) | (~spl6_7 | ~spl6_10)),
% 13.46/2.12    inference(forward_demodulation,[],[f4028,f1044])).
% 13.46/2.12  fof(f4028,plain,(
% 13.46/2.12    ( ! [X81] : (k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X81,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))) ) | (~spl6_7 | ~spl6_10)),
% 13.46/2.12    inference(forward_demodulation,[],[f4027,f529])).
% 13.46/2.12  fof(f529,plain,(
% 13.46/2.12    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X12,X12))) = k3_tarski(k6_enumset1(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X13),k4_xboole_0(X12,X12)))) )),
% 13.46/2.12    inference(superposition,[],[f116,f199])).
% 13.46/2.12  fof(f4027,plain,(
% 13.46/2.12    ( ! [X81] : (k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X81,sK1)) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)))) ) | (~spl6_7 | ~spl6_10)),
% 13.46/2.12    inference(forward_demodulation,[],[f3890,f1044])).
% 13.46/2.12  fof(f3890,plain,(
% 13.46/2.12    ( ! [X81] : (k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X81,sK1)) = k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(k4_xboole_0(sK1,sK0),X81),k4_xboole_0(sK1,sK1)))) ) | ~spl6_10),
% 13.46/2.12    inference(superposition,[],[f367,f275])).
% 13.46/2.12  fof(f4020,plain,(
% 13.46/2.12    spl6_57 | ~spl6_7 | ~spl6_10),
% 13.46/2.12    inference(avatar_split_clause,[],[f4015,f273,f209,f4017])).
% 13.46/2.12  fof(f4017,plain,(
% 13.46/2.12    spl6_57 <=> k4_xboole_0(sK1,sK0) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0)))),
% 13.46/2.12    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 13.46/2.12  fof(f4015,plain,(
% 13.46/2.12    k4_xboole_0(sK1,sK0) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0))) | (~spl6_7 | ~spl6_10)),
% 13.46/2.12    inference(forward_demodulation,[],[f4014,f1044])).
% 13.46/2.13  fof(f4014,plain,(
% 13.46/2.13    ( ! [X77] : (k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),X77)) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0)))) ) | (~spl6_7 | ~spl6_10)),
% 13.46/2.13    inference(forward_demodulation,[],[f3886,f1044])).
% 13.46/2.13  fof(f3886,plain,(
% 13.46/2.13    ( ! [X77] : (k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),X77)) = k3_tarski(k6_enumset1(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),X77))))) ) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f361,f275])).
% 13.46/2.13  fof(f4013,plain,(
% 13.46/2.13    ~spl6_43 | spl6_56 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f4009,f273,f4011,f3904])).
% 13.46/2.13  fof(f4011,plain,(
% 13.46/2.13    spl6_56 <=> ! [X76] : (k4_xboole_0(sK1,sK1) = X76 | r2_hidden(sK4(sK1,sK1,X76),X76) | r2_hidden(sK4(sK1,sK1,X76),sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 13.46/2.13  fof(f4009,plain,(
% 13.46/2.13    ( ! [X76] : (k4_xboole_0(sK1,sK1) = X76 | r2_hidden(sK4(sK1,sK1,X76),sK1) | r2_hidden(sK4(sK1,sK1,X76),X76) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(forward_demodulation,[],[f3897,f525])).
% 13.46/2.13  fof(f3897,plain,(
% 13.46/2.13    ( ! [X76] : (r2_hidden(sK4(sK1,sK1,X76),sK1) | k5_xboole_0(sK1,sK1) = X76 | r2_hidden(sK4(sK1,sK1,X76),X76) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(duplicate_literal_removal,[],[f3885])).
% 13.46/2.13  fof(f3885,plain,(
% 13.46/2.13    ( ! [X76] : (r2_hidden(sK4(sK1,sK1,X76),sK1) | r2_hidden(sK4(sK1,sK1,X76),sK1) | k5_xboole_0(sK1,sK1) = X76 | r2_hidden(sK4(sK1,sK1,X76),X76) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f350,f275])).
% 13.46/2.13  fof(f350,plain,(
% 13.46/2.13    ( ! [X6,X8,X7] : (r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),k4_xboole_0(X6,X7)) | r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X6) | k5_xboole_0(k4_xboole_0(X6,X7),X6) = X8 | r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X8) | ~r1_tarski(X6,X7)) )),
% 13.46/2.13    inference(superposition,[],[f147,f115])).
% 13.46/2.13  fof(f3995,plain,(
% 13.46/2.13    ~spl6_43 | spl6_55 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3991,f273,f3993,f3904])).
% 13.46/2.13  fof(f3993,plain,(
% 13.46/2.13    spl6_55 <=> ! [X65] : (k4_xboole_0(sK1,sK1) = X65 | ~r2_hidden(sK4(sK1,sK1,X65),sK1) | ~r2_hidden(sK4(sK1,sK1,X65),X65))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 13.46/2.13  fof(f3991,plain,(
% 13.46/2.13    ( ! [X65] : (k4_xboole_0(sK1,sK1) = X65 | ~r2_hidden(sK4(sK1,sK1,X65),X65) | ~r2_hidden(sK4(sK1,sK1,X65),sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(forward_demodulation,[],[f3877,f525])).
% 13.46/2.13  fof(f3877,plain,(
% 13.46/2.13    ( ! [X65] : (~r2_hidden(sK4(sK1,sK1,X65),X65) | ~r2_hidden(sK4(sK1,sK1,X65),sK1) | k5_xboole_0(sK1,sK1) = X65 | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f320,f275])).
% 13.46/2.13  fof(f320,plain,(
% 13.46/2.13    ( ! [X6,X8,X7] : (~r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X8) | ~r2_hidden(sK4(k4_xboole_0(X6,X7),X6,X8),X6) | k5_xboole_0(k4_xboole_0(X6,X7),X6) = X8 | ~r1_tarski(X6,X7)) )),
% 13.46/2.13    inference(superposition,[],[f145,f115])).
% 13.46/2.13  fof(f145,plain,(
% 13.46/2.13    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.46/2.13    inference(forward_demodulation,[],[f118,f114])).
% 13.46/2.13  fof(f118,plain,(
% 13.46/2.13    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.46/2.13    inference(definition_unfolding,[],[f95,f111])).
% 13.46/2.13  fof(f95,plain,(
% 13.46/2.13    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 13.46/2.13    inference(cnf_transformation,[],[f53])).
% 13.46/2.13  fof(f3987,plain,(
% 13.46/2.13    ~spl6_43 | spl6_54 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3983,f273,f3985,f3904])).
% 13.46/2.13  fof(f3985,plain,(
% 13.46/2.13    spl6_54 <=> ! [X62] : (k4_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X62)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 13.46/2.13  fof(f3983,plain,(
% 13.46/2.13    ( ! [X62] : (k4_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X62)) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(forward_demodulation,[],[f3899,f525])).
% 13.46/2.13  fof(f3899,plain,(
% 13.46/2.13    ( ! [X62] : (k5_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X62)) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(duplicate_literal_removal,[],[f3874])).
% 13.46/2.13  fof(f3874,plain,(
% 13.46/2.13    ( ! [X62] : (k5_xboole_0(sK1,sK1) = k4_subset_1(X62,sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X62)) | ~m1_subset_1(sK1,k1_zfmisc_1(X62)) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f308,f275])).
% 13.46/2.13  fof(f308,plain,(
% 13.46/2.13    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),X6) = k4_subset_1(X8,k4_xboole_0(X6,X7),X6) | ~m1_subset_1(X6,k1_zfmisc_1(X8)) | ~m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(X8)) | ~r1_tarski(X6,X7)) )),
% 13.46/2.13    inference(superposition,[],[f144,f115])).
% 13.46/2.13  fof(f3963,plain,(
% 13.46/2.13    spl6_53 | ~spl6_7 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3958,f273,f209,f3960])).
% 13.46/2.13  fof(f3960,plain,(
% 13.46/2.13    spl6_53 <=> k4_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 13.46/2.13  fof(f3958,plain,(
% 13.46/2.13    k4_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) | (~spl6_7 | ~spl6_10)),
% 13.46/2.13    inference(forward_demodulation,[],[f3848,f1044])).
% 13.46/2.13  fof(f3848,plain,(
% 13.46/2.13    k4_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1))) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f240,f275])).
% 13.46/2.13  fof(f240,plain,(
% 13.46/2.13    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))))) )),
% 13.46/2.13    inference(superposition,[],[f112,f113])).
% 13.46/2.13  fof(f3957,plain,(
% 13.46/2.13    spl6_52 | ~spl6_7 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3952,f273,f209,f3954])).
% 13.46/2.13  fof(f3954,plain,(
% 13.46/2.13    spl6_52 <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 13.46/2.13  fof(f3952,plain,(
% 13.46/2.13    k4_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)) | (~spl6_7 | ~spl6_10)),
% 13.46/2.13    inference(forward_demodulation,[],[f3847,f1044])).
% 13.46/2.13  fof(f3847,plain,(
% 13.46/2.13    k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f238,f275])).
% 13.46/2.13  fof(f3951,plain,(
% 13.46/2.13    ~spl6_50 | spl6_51 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3846,f273,f3948,f3944])).
% 13.46/2.13  fof(f3846,plain,(
% 13.46/2.13    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1) | ~r1_tarski(k4_xboole_0(sK1,sK0),sK1) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f236,f275])).
% 13.46/2.13  fof(f3942,plain,(
% 13.46/2.13    ~spl6_43 | spl6_44 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3941,f273,f3908,f3904])).
% 13.46/2.13  fof(f3941,plain,(
% 13.46/2.13    sK1 = k4_xboole_0(sK1,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.13    inference(forward_demodulation,[],[f3845,f525])).
% 13.46/2.13  fof(f3845,plain,(
% 13.46/2.13    sK1 = k5_xboole_0(sK1,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f235,f275])).
% 13.46/2.13  fof(f3940,plain,(
% 13.46/2.13    ~spl6_43 | spl6_49 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3936,f273,f3938,f3904])).
% 13.46/2.13  fof(f3938,plain,(
% 13.46/2.13    spl6_49 <=> ! [X31] : (r2_hidden(X31,k4_xboole_0(sK1,sK1)) | ~r2_hidden(X31,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 13.46/2.13  fof(f3936,plain,(
% 13.46/2.13    ( ! [X31] : (r2_hidden(X31,k4_xboole_0(sK1,sK1)) | ~r2_hidden(X31,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(forward_demodulation,[],[f3843,f525])).
% 13.46/2.13  fof(f3843,plain,(
% 13.46/2.13    ( ! [X31] : (r2_hidden(X31,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X31,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f216,f275])).
% 13.46/2.13  fof(f216,plain,(
% 13.46/2.13    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(k4_xboole_0(X0,X1),X0)) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 13.46/2.13    inference(superposition,[],[f148,f115])).
% 13.46/2.13  fof(f3935,plain,(
% 13.46/2.13    ~spl6_43 | spl6_48 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3842,f273,f3933,f3904])).
% 13.46/2.13  fof(f3933,plain,(
% 13.46/2.13    spl6_48 <=> ! [X30] : ~r2_hidden(X30,sK1)),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 13.46/2.13  fof(f3842,plain,(
% 13.46/2.13    ( ! [X30] : (~r2_hidden(X30,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0))) ) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f203,f275])).
% 13.46/2.13  fof(f3931,plain,(
% 13.46/2.13    ~spl6_43 | spl6_44 | ~spl6_47 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3841,f273,f3928,f3908,f3904])).
% 13.46/2.13  fof(f3841,plain,(
% 13.46/2.13    ~r1_tarski(sK1,sK1) | sK1 = k4_xboole_0(sK1,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f200,f275])).
% 13.46/2.13  fof(f200,plain,(
% 13.46/2.13    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X0) = X0 | ~r1_tarski(X0,X1)) )),
% 13.46/2.13    inference(superposition,[],[f115,f115])).
% 13.46/2.13  fof(f3923,plain,(
% 13.46/2.13    ~spl6_43 | spl6_44 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3828,f273,f3908,f3904])).
% 13.46/2.13  fof(f3828,plain,(
% 13.46/2.13    sK1 = k4_xboole_0(sK1,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f115,f275])).
% 13.46/2.13  fof(f3921,plain,(
% 13.46/2.13    spl6_46 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3808,f273,f3918])).
% 13.46/2.13  fof(f3918,plain,(
% 13.46/2.13    spl6_46 <=> sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 13.46/2.13  fof(f3808,plain,(
% 13.46/2.13    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f240,f275])).
% 13.46/2.13  fof(f3916,plain,(
% 13.46/2.13    spl6_45 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3807,f273,f3913])).
% 13.46/2.13  fof(f3913,plain,(
% 13.46/2.13    spl6_45 <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 13.46/2.13  fof(f3807,plain,(
% 13.46/2.13    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f238,f275])).
% 13.46/2.13  fof(f3911,plain,(
% 13.46/2.13    ~spl6_43 | spl6_44 | ~spl6_10),
% 13.46/2.13    inference(avatar_split_clause,[],[f3902,f273,f3908,f3904])).
% 13.46/2.13  fof(f3902,plain,(
% 13.46/2.13    sK1 = k4_xboole_0(sK1,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.13    inference(forward_demodulation,[],[f3801,f525])).
% 13.46/2.13  fof(f3801,plain,(
% 13.46/2.13    sK1 = k5_xboole_0(sK1,sK1) | ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_10),
% 13.46/2.13    inference(superposition,[],[f275,f235])).
% 13.46/2.13  fof(f2779,plain,(
% 13.46/2.13    spl6_42 | ~spl6_4 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f2744,f209,f169,f2776])).
% 13.46/2.13  fof(f2776,plain,(
% 13.46/2.13    spl6_42 <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 13.46/2.13  fof(f2744,plain,(
% 13.46/2.13    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f171,f542,f542,f542,f542,f360])).
% 13.46/2.13  fof(f2409,plain,(
% 13.46/2.13    ~spl6_2 | ~spl6_22 | spl6_41 | spl6_9),
% 13.46/2.13    inference(avatar_split_clause,[],[f2373,f230,f2401,f435,f140])).
% 13.46/2.13  fof(f2401,plain,(
% 13.46/2.13    spl6_41 <=> ! [X0] : (~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 13.46/2.13  fof(f230,plain,(
% 13.46/2.13    spl6_9 <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 13.46/2.13  fof(f2373,plain,(
% 13.46/2.13    ( ! [X1] : (sK0 != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X1))) ) | spl6_9),
% 13.46/2.13    inference(superposition,[],[f232,f309])).
% 13.46/2.13  fof(f232,plain,(
% 13.46/2.13    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | spl6_9),
% 13.46/2.13    inference(avatar_component_clause,[],[f230])).
% 13.46/2.13  fof(f2408,plain,(
% 13.46/2.13    ~spl6_2 | ~spl6_22 | spl6_41 | spl6_3 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f2407,f225,f153,f2401,f435,f140])).
% 13.46/2.13  fof(f153,plain,(
% 13.46/2.13    spl6_3 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 13.46/2.13  fof(f2407,plain,(
% 13.46/2.13    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (spl6_3 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f2406,f227])).
% 13.46/2.13  fof(f2406,plain,(
% 13.46/2.13    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (spl6_3 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f2405,f227])).
% 13.46/2.13  fof(f2405,plain,(
% 13.46/2.13    ( ! [X0] : (sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (spl6_3 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f2372,f227])).
% 13.46/2.13  fof(f2372,plain,(
% 13.46/2.13    ( ! [X0] : (sK0 != k4_subset_1(X0,sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | spl6_3),
% 13.46/2.13    inference(superposition,[],[f155,f309])).
% 13.46/2.13  fof(f155,plain,(
% 13.46/2.13    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl6_3),
% 13.46/2.13    inference(avatar_component_clause,[],[f153])).
% 13.46/2.13  fof(f2404,plain,(
% 13.46/2.13    ~spl6_2 | ~spl6_22 | spl6_41 | spl6_9),
% 13.46/2.13    inference(avatar_split_clause,[],[f2366,f230,f2401,f435,f140])).
% 13.46/2.13  fof(f2366,plain,(
% 13.46/2.13    ( ! [X1] : (sK0 != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | spl6_9),
% 13.46/2.13    inference(superposition,[],[f232,f309])).
% 13.46/2.13  fof(f2403,plain,(
% 13.46/2.13    ~spl6_2 | spl6_41 | ~spl6_22 | spl6_3 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f2399,f225,f153,f435,f2401,f140])).
% 13.46/2.13  fof(f2399,plain,(
% 13.46/2.13    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | (spl6_3 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f2398,f227])).
% 13.46/2.13  fof(f2398,plain,(
% 13.46/2.13    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | (spl6_3 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f2397,f227])).
% 13.46/2.13  fof(f2397,plain,(
% 13.46/2.13    ( ! [X0] : (sK0 != k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | (spl6_3 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f2365,f227])).
% 13.46/2.13  fof(f2365,plain,(
% 13.46/2.13    ( ! [X0] : (sK0 != k4_subset_1(X0,sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) ) | spl6_3),
% 13.46/2.13    inference(superposition,[],[f155,f309])).
% 13.46/2.13  fof(f2229,plain,(
% 13.46/2.13    spl6_40 | ~spl6_36),
% 13.46/2.13    inference(avatar_split_clause,[],[f2211,f1747,f2226])).
% 13.46/2.13  fof(f2226,plain,(
% 13.46/2.13    spl6_40 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 13.46/2.13  fof(f2211,plain,(
% 13.46/2.13    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | ~spl6_36),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f1749,f115])).
% 13.46/2.13  fof(f2224,plain,(
% 13.46/2.13    spl6_39 | ~spl6_36),
% 13.46/2.13    inference(avatar_split_clause,[],[f2214,f1747,f2221])).
% 13.46/2.13  fof(f2221,plain,(
% 13.46/2.13    spl6_39 <=> k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 13.46/2.13  fof(f2214,plain,(
% 13.46/2.13    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_36),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f1749,f235])).
% 13.46/2.13  fof(f2210,plain,(
% 13.46/2.13    spl6_38 | ~spl6_4 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f2184,f209,f169,f2207])).
% 13.46/2.13  fof(f2207,plain,(
% 13.46/2.13    spl6_38 <=> r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 13.46/2.13  fof(f2184,plain,(
% 13.46/2.13    r2_hidden(sK4(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f171,f542,f542,f542,f359])).
% 13.46/2.13  fof(f2180,plain,(
% 13.46/2.13    spl6_37 | ~spl6_4 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f2154,f209,f169,f2177])).
% 13.46/2.13  fof(f2177,plain,(
% 13.46/2.13    spl6_37 <=> r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 13.46/2.13  fof(f2154,plain,(
% 13.46/2.13    r2_hidden(sK4(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)),k1_zfmisc_1(sK0)) | (~spl6_4 | ~spl6_7)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f171,f542,f542,f542,f358])).
% 13.46/2.13  fof(f1751,plain,(
% 13.46/2.13    spl6_36 | ~spl6_15),
% 13.46/2.13    inference(avatar_split_clause,[],[f1739,f387,f1747])).
% 13.46/2.13  fof(f1739,plain,(
% 13.46/2.13    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl6_15),
% 13.46/2.13    inference(resolution,[],[f389,f127])).
% 13.46/2.13  fof(f1750,plain,(
% 13.46/2.13    spl6_36 | ~spl6_15),
% 13.46/2.13    inference(avatar_split_clause,[],[f1731,f387,f1747])).
% 13.46/2.13  fof(f1731,plain,(
% 13.46/2.13    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl6_15),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f389,f127])).
% 13.46/2.13  fof(f1745,plain,(
% 13.46/2.13    spl6_35 | ~spl6_7 | ~spl6_15),
% 13.46/2.13    inference(avatar_split_clause,[],[f1733,f387,f209,f1742])).
% 13.46/2.13  fof(f1742,plain,(
% 13.46/2.13    spl6_35 <=> r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 13.46/2.13  fof(f1733,plain,(
% 13.46/2.13    r2_hidden(k4_xboole_0(sK0,sK1),k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0))) | (~spl6_7 | ~spl6_15)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f542,f389,f131])).
% 13.46/2.13  fof(f1384,plain,(
% 13.46/2.13    spl6_34 | ~spl6_4),
% 13.46/2.13    inference(avatar_split_clause,[],[f1365,f169,f1381])).
% 13.46/2.13  fof(f1381,plain,(
% 13.46/2.13    spl6_34 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 13.46/2.13  fof(f1365,plain,(
% 13.46/2.13    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) | ~spl6_4),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f161,f205,f256])).
% 13.46/2.13  fof(f256,plain,(
% 13.46/2.13    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | r2_hidden(X2,k4_xboole_0(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 13.46/2.13    inference(superposition,[],[f131,f113])).
% 13.46/2.13  fof(f1071,plain,(
% 13.46/2.13    spl6_33 | ~spl6_4 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f1028,f209,f169,f1068])).
% 13.46/2.13  fof(f1068,plain,(
% 13.46/2.13    spl6_33 <=> r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 13.46/2.13  fof(f1028,plain,(
% 13.46/2.13    r2_hidden(sK1,k4_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(sK1,sK0))) | (~spl6_4 | ~spl6_7)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f171,f542,f131])).
% 13.46/2.13  fof(f1065,plain,(
% 13.46/2.13    ~spl6_32 | ~spl6_7 | spl6_14),
% 13.46/2.13    inference(avatar_split_clause,[],[f1060,f329,f209,f1062])).
% 13.46/2.13  fof(f1062,plain,(
% 13.46/2.13    spl6_32 <=> r2_hidden(sK0,k5_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 13.46/2.13  fof(f1060,plain,(
% 13.46/2.13    ~r2_hidden(sK0,k5_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0))) | (~spl6_7 | spl6_14)),
% 13.46/2.13    inference(forward_demodulation,[],[f1031,f1044])).
% 13.46/2.13  fof(f1031,plain,(
% 13.46/2.13    ~r2_hidden(sK0,k5_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k1_zfmisc_1(sK1)))) | (~spl6_7 | spl6_14)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f331,f542,f150])).
% 13.46/2.13  fof(f1058,plain,(
% 13.46/2.13    ~spl6_31 | ~spl6_7 | spl6_14),
% 13.46/2.13    inference(avatar_split_clause,[],[f1033,f329,f209,f1055])).
% 13.46/2.13  fof(f1055,plain,(
% 13.46/2.13    spl6_31 <=> r2_hidden(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0))))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 13.46/2.13  fof(f1033,plain,(
% 13.46/2.13    ~r2_hidden(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k1_zfmisc_1(sK1),k4_xboole_0(sK1,sK0)))) | (~spl6_7 | spl6_14)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f331,f542,f150])).
% 13.46/2.13  fof(f830,plain,(
% 13.46/2.13    ~spl6_30 | spl6_14),
% 13.46/2.13    inference(avatar_split_clause,[],[f810,f329,f827])).
% 13.46/2.13  fof(f827,plain,(
% 13.46/2.13    spl6_30 <=> r2_hidden(sK0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 13.46/2.13  fof(f810,plain,(
% 13.46/2.13    ~r2_hidden(sK0,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))) | spl6_14),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f124,f331,f292])).
% 13.46/2.13  fof(f292,plain,(
% 13.46/2.13    ( ! [X6,X8,X7] : (~r2_hidden(X8,k5_xboole_0(k4_xboole_0(X6,X7),X6)) | r2_hidden(X8,X6) | ~r1_tarski(X6,X7)) )),
% 13.46/2.13    inference(global_subsumption,[],[f133,f291])).
% 13.46/2.13  fof(f291,plain,(
% 13.46/2.13    ( ! [X6,X8,X7] : (~r2_hidden(X8,k5_xboole_0(k4_xboole_0(X6,X7),X6)) | r2_hidden(X8,X6) | r2_hidden(X8,k4_xboole_0(X6,X7)) | ~r1_tarski(X6,X7)) )),
% 13.46/2.13    inference(superposition,[],[f150,f115])).
% 13.46/2.13  fof(f808,plain,(
% 13.46/2.13    spl6_29 | ~spl6_4),
% 13.46/2.13    inference(avatar_split_clause,[],[f793,f169,f805])).
% 13.46/2.13  fof(f793,plain,(
% 13.46/2.13    r2_hidden(sK1,k5_xboole_0(k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))) | ~spl6_4),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f124,f171,f216])).
% 13.46/2.13  fof(f710,plain,(
% 13.46/2.13    spl6_28 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f675,f209,f707])).
% 13.46/2.13  fof(f675,plain,(
% 13.46/2.13    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_7),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f211,f236])).
% 13.46/2.13  fof(f670,plain,(
% 13.46/2.13    spl6_27 | spl6_14),
% 13.46/2.13    inference(avatar_split_clause,[],[f657,f329,f667])).
% 13.46/2.13  fof(f667,plain,(
% 13.46/2.13    spl6_27 <=> r2_hidden(sK0,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 13.46/2.13  fof(f657,plain,(
% 13.46/2.13    r2_hidden(sK0,k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) | spl6_14),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f161,f331,f131])).
% 13.46/2.13  fof(f665,plain,(
% 13.46/2.13    ~spl6_26 | spl6_14),
% 13.46/2.13    inference(avatar_split_clause,[],[f659,f329,f662])).
% 13.46/2.13  fof(f662,plain,(
% 13.46/2.13    spl6_26 <=> m1_subset_1(sK0,k1_zfmisc_1(sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 13.46/2.13  fof(f659,plain,(
% 13.46/2.13    ~m1_subset_1(sK0,k1_zfmisc_1(sK1)) | spl6_14),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f61,f331,f71])).
% 13.46/2.13  fof(f616,plain,(
% 13.46/2.13    spl6_25 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f578,f209,f613])).
% 13.46/2.13  fof(f613,plain,(
% 13.46/2.13    spl6_25 <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 13.46/2.13  fof(f578,plain,(
% 13.46/2.13    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) | ~spl6_7),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f211,f235])).
% 13.46/2.13  fof(f565,plain,(
% 13.46/2.13    spl6_24 | ~spl6_6 | ~spl6_8 | ~spl6_17),
% 13.46/2.13    inference(avatar_split_clause,[],[f560,f399,f225,f193,f562])).
% 13.46/2.13  fof(f399,plain,(
% 13.46/2.13    spl6_17 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 13.46/2.13  fof(f560,plain,(
% 13.46/2.13    r2_hidden(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_8 | ~spl6_17)),
% 13.46/2.13    inference(forward_demodulation,[],[f559,f401])).
% 13.46/2.13  fof(f401,plain,(
% 13.46/2.13    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_17),
% 13.46/2.13    inference(avatar_component_clause,[],[f399])).
% 13.46/2.13  fof(f559,plain,(
% 13.46/2.13    r2_hidden(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f554,f227])).
% 13.46/2.13  fof(f554,plain,(
% 13.46/2.13    r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_6),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f195,f197])).
% 13.46/2.13  fof(f197,plain,(
% 13.46/2.13    ( ! [X0,X1] : (r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 13.46/2.13    inference(global_subsumption,[],[f61,f190])).
% 13.46/2.13  fof(f190,plain,(
% 13.46/2.13    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 13.46/2.13    inference(resolution,[],[f76,f71])).
% 13.46/2.13  fof(f498,plain,(
% 13.46/2.13    spl6_23),
% 13.46/2.13    inference(avatar_split_clause,[],[f497,f493])).
% 13.46/2.13  fof(f493,plain,(
% 13.46/2.13    spl6_23 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 13.46/2.13  fof(f497,plain,(
% 13.46/2.13    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 13.46/2.13    inference(global_subsumption,[],[f468])).
% 13.46/2.13  fof(f468,plain,(
% 13.46/2.13    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 13.46/2.13    inference(superposition,[],[f198,f198])).
% 13.46/2.13  fof(f496,plain,(
% 13.46/2.13    spl6_23),
% 13.46/2.13    inference(avatar_split_clause,[],[f468,f493])).
% 13.46/2.13  fof(f438,plain,(
% 13.46/2.13    spl6_22 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f431,f225,f193,f435])).
% 13.46/2.13  fof(f431,plain,(
% 13.46/2.13    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(superposition,[],[f195,f227])).
% 13.46/2.13  fof(f430,plain,(
% 13.46/2.13    spl6_21 | ~spl6_16 | ~spl6_17),
% 13.46/2.13    inference(avatar_split_clause,[],[f425,f399,f393,f427])).
% 13.46/2.13  fof(f393,plain,(
% 13.46/2.13    spl6_16 <=> m1_subset_1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 13.46/2.13  fof(f425,plain,(
% 13.46/2.13    m1_subset_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | (~spl6_16 | ~spl6_17)),
% 13.46/2.13    inference(forward_demodulation,[],[f395,f401])).
% 13.46/2.13  fof(f395,plain,(
% 13.46/2.13    m1_subset_1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_16),
% 13.46/2.13    inference(avatar_component_clause,[],[f393])).
% 13.46/2.13  fof(f424,plain,(
% 13.46/2.13    spl6_5 | spl6_15 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f423,f225,f193,f387,f174])).
% 13.46/2.13  fof(f174,plain,(
% 13.46/2.13    spl6_5 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 13.46/2.13  fof(f423,plain,(
% 13.46/2.13    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f382,f227])).
% 13.46/2.13  fof(f382,plain,(
% 13.46/2.13    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_6),
% 13.46/2.13    inference(resolution,[],[f195,f71])).
% 13.46/2.13  fof(f422,plain,(
% 13.46/2.13    spl6_20 | ~spl6_2 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f417,f225,f193,f140,f419])).
% 13.46/2.13  fof(f417,plain,(
% 13.46/2.13    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | (~spl6_2 | ~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f375,f227])).
% 13.46/2.13  fof(f375,plain,(
% 13.46/2.13    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) | (~spl6_2 | ~spl6_6)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f142,f195,f144])).
% 13.46/2.13  fof(f416,plain,(
% 13.46/2.13    spl6_18 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f415,f225,f193,f405])).
% 13.46/2.13  fof(f405,plain,(
% 13.46/2.13    spl6_18 <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 13.46/2.13  fof(f415,plain,(
% 13.46/2.13    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f376,f227])).
% 13.46/2.13  fof(f376,plain,(
% 13.46/2.13    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) | ~spl6_6),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f195,f195,f144])).
% 13.46/2.13  fof(f414,plain,(
% 13.46/2.13    spl6_19 | ~spl6_2 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f409,f225,f193,f140,f411])).
% 13.46/2.13  fof(f409,plain,(
% 13.46/2.13    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | (~spl6_2 | ~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f377,f227])).
% 13.46/2.13  fof(f377,plain,(
% 13.46/2.13    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,sK1),sK1)) | (~spl6_2 | ~spl6_6)),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f142,f195,f144])).
% 13.46/2.13  fof(f408,plain,(
% 13.46/2.13    spl6_18 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f403,f225,f193,f405])).
% 13.46/2.13  fof(f403,plain,(
% 13.46/2.13    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f378,f227])).
% 13.46/2.13  fof(f378,plain,(
% 13.46/2.13    k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) | ~spl6_6),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f195,f195,f144])).
% 13.46/2.13  fof(f402,plain,(
% 13.46/2.13    spl6_17 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f397,f225,f193,f399])).
% 13.46/2.13  fof(f397,plain,(
% 13.46/2.13    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f379,f227])).
% 13.46/2.13  fof(f379,plain,(
% 13.46/2.13    k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl6_6),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f195,f77])).
% 13.46/2.13  fof(f396,plain,(
% 13.46/2.13    spl6_16 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f391,f225,f193,f393])).
% 13.46/2.13  fof(f391,plain,(
% 13.46/2.13    m1_subset_1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f380,f227])).
% 13.46/2.13  fof(f380,plain,(
% 13.46/2.13    m1_subset_1(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_6),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f195,f76])).
% 13.46/2.13  fof(f390,plain,(
% 13.46/2.13    spl6_15 | ~spl6_6 | ~spl6_8),
% 13.46/2.13    inference(avatar_split_clause,[],[f385,f225,f193,f387])).
% 13.46/2.13  fof(f385,plain,(
% 13.46/2.13    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_8)),
% 13.46/2.13    inference(forward_demodulation,[],[f381,f227])).
% 13.46/2.13  fof(f381,plain,(
% 13.46/2.13    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_6),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f61,f195,f71])).
% 13.46/2.13  fof(f332,plain,(
% 13.46/2.13    ~spl6_14 | spl6_11),
% 13.46/2.13    inference(avatar_split_clause,[],[f327,f278,f329])).
% 13.46/2.13  fof(f278,plain,(
% 13.46/2.13    spl6_11 <=> r1_tarski(sK0,sK1)),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 13.46/2.13  fof(f327,plain,(
% 13.46/2.13    ~r2_hidden(sK0,k1_zfmisc_1(sK1)) | spl6_11),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f280,f127])).
% 13.46/2.13  fof(f280,plain,(
% 13.46/2.13    ~r1_tarski(sK0,sK1) | spl6_11),
% 13.46/2.13    inference(avatar_component_clause,[],[f278])).
% 13.46/2.13  fof(f317,plain,(
% 13.46/2.13    spl6_13 | ~spl6_2),
% 13.46/2.13    inference(avatar_split_clause,[],[f305,f140,f314])).
% 13.46/2.13  fof(f305,plain,(
% 13.46/2.13    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | ~spl6_2),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f142,f142,f144])).
% 13.46/2.13  fof(f285,plain,(
% 13.46/2.13    ~spl6_11 | spl6_12 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f271,f209,f282,f278])).
% 13.46/2.13  fof(f282,plain,(
% 13.46/2.13    spl6_12 <=> sK0 = sK1),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 13.46/2.13  fof(f271,plain,(
% 13.46/2.13    sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~spl6_7),
% 13.46/2.13    inference(resolution,[],[f211,f82])).
% 13.46/2.13  fof(f82,plain,(
% 13.46/2.13    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 13.46/2.13    inference(cnf_transformation,[],[f44])).
% 13.46/2.13  fof(f276,plain,(
% 13.46/2.13    spl6_10 | ~spl6_7),
% 13.46/2.13    inference(avatar_split_clause,[],[f269,f209,f273])).
% 13.46/2.13  fof(f269,plain,(
% 13.46/2.13    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl6_7),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f211,f115])).
% 13.46/2.13  fof(f233,plain,(
% 13.46/2.13    ~spl6_2 | ~spl6_9 | spl6_3),
% 13.46/2.13    inference(avatar_split_clause,[],[f221,f153,f230,f140])).
% 13.46/2.13  fof(f221,plain,(
% 13.46/2.13    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl6_3),
% 13.46/2.13    inference(superposition,[],[f155,f77])).
% 13.46/2.13  fof(f228,plain,(
% 13.46/2.13    spl6_8 | ~spl6_2),
% 13.46/2.13    inference(avatar_split_clause,[],[f220,f140,f225])).
% 13.46/2.13  fof(f220,plain,(
% 13.46/2.13    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl6_2),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f142,f77])).
% 13.46/2.13  fof(f213,plain,(
% 13.46/2.13    spl6_7 | ~spl6_4),
% 13.46/2.13    inference(avatar_split_clause,[],[f207,f169,f209])).
% 13.46/2.13  fof(f207,plain,(
% 13.46/2.13    r1_tarski(sK1,sK0) | ~spl6_4),
% 13.46/2.13    inference(resolution,[],[f171,f127])).
% 13.46/2.13  fof(f212,plain,(
% 13.46/2.13    spl6_7 | ~spl6_4),
% 13.46/2.13    inference(avatar_split_clause,[],[f204,f169,f209])).
% 13.46/2.13  fof(f204,plain,(
% 13.46/2.13    r1_tarski(sK1,sK0) | ~spl6_4),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f171,f127])).
% 13.46/2.13  fof(f196,plain,(
% 13.46/2.13    spl6_6 | ~spl6_2),
% 13.46/2.13    inference(avatar_split_clause,[],[f189,f140,f193])).
% 13.46/2.13  fof(f189,plain,(
% 13.46/2.13    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_2),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f142,f76])).
% 13.46/2.13  fof(f177,plain,(
% 13.46/2.13    spl6_5 | spl6_4 | ~spl6_2),
% 13.46/2.13    inference(avatar_split_clause,[],[f166,f140,f169,f174])).
% 13.46/2.13  fof(f166,plain,(
% 13.46/2.13    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_2),
% 13.46/2.13    inference(resolution,[],[f71,f142])).
% 13.46/2.13  fof(f172,plain,(
% 13.46/2.13    spl6_4 | ~spl6_2),
% 13.46/2.13    inference(avatar_split_clause,[],[f165,f140,f169])).
% 13.46/2.13  fof(f165,plain,(
% 13.46/2.13    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl6_2),
% 13.46/2.13    inference(unit_resulting_resolution,[],[f61,f142,f71])).
% 13.46/2.13  fof(f156,plain,(
% 13.46/2.13    ~spl6_3 | spl6_1),
% 13.46/2.13    inference(avatar_split_clause,[],[f151,f135,f153])).
% 13.46/2.13  fof(f135,plain,(
% 13.46/2.13    spl6_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 13.46/2.13    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 13.46/2.13  fof(f151,plain,(
% 13.46/2.13    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl6_1),
% 13.46/2.13    inference(forward_demodulation,[],[f137,f63])).
% 13.46/2.13  fof(f63,plain,(
% 13.46/2.13    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 13.46/2.13    inference(cnf_transformation,[],[f22])).
% 13.46/2.13  fof(f22,axiom,(
% 13.46/2.13    ! [X0] : k2_subset_1(X0) = X0),
% 13.46/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 13.46/2.13  fof(f137,plain,(
% 13.46/2.13    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl6_1),
% 13.46/2.13    inference(avatar_component_clause,[],[f135])).
% 13.46/2.13  fof(f143,plain,(
% 13.46/2.13    spl6_2),
% 13.46/2.13    inference(avatar_split_clause,[],[f59,f140])).
% 13.46/2.13  fof(f59,plain,(
% 13.46/2.13    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 13.46/2.13    inference(cnf_transformation,[],[f38])).
% 13.46/2.13  fof(f38,plain,(
% 13.46/2.13    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 13.46/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f37])).
% 13.46/2.13  fof(f37,plain,(
% 13.46/2.13    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 13.46/2.13    introduced(choice_axiom,[])).
% 13.46/2.13  fof(f29,plain,(
% 13.46/2.13    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.46/2.13    inference(ennf_transformation,[],[f28])).
% 13.46/2.13  fof(f28,negated_conjecture,(
% 13.46/2.13    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 13.46/2.13    inference(negated_conjecture,[],[f27])).
% 13.46/2.13  fof(f27,conjecture,(
% 13.46/2.13    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 13.46/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 13.46/2.13  fof(f138,plain,(
% 13.46/2.13    ~spl6_1),
% 13.46/2.13    inference(avatar_split_clause,[],[f60,f135])).
% 13.46/2.13  fof(f60,plain,(
% 13.46/2.13    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 13.46/2.13    inference(cnf_transformation,[],[f38])).
% 13.46/2.13  % SZS output end Proof for theBenchmark
% 13.46/2.13  % (24549)------------------------------
% 13.46/2.13  % (24549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.46/2.13  % (24549)Termination reason: Refutation
% 13.46/2.13  
% 13.46/2.13  % (24549)Memory used [KB]: 18038
% 13.46/2.13  % (24549)Time elapsed: 1.670 s
% 13.46/2.13  % (24549)------------------------------
% 13.46/2.13  % (24549)------------------------------
% 13.99/2.14  % (24530)Success in time 1.785 s
%------------------------------------------------------------------------------
