%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t135_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:58 EDT 2019

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  721 (2828 expanded)
%              Number of leaves         :  111 ( 882 expanded)
%              Depth                    :   16
%              Number of atoms          : 2049 (9113 expanded)
%              Number of equality atoms :  413 (3873 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f138,f192,f199,f214,f221,f562,f575,f601,f616,f656,f669,f721,f728,f3092,f3186,f3280,f3374,f3817,f3852,f3865,f3868,f3873,f3909,f3912,f3916,f3953,f3992,f4038,f4075,f4113,f4154,f4196,f4239,f4263,f4270,f4284,f4291,f4305,f4312,f4326,f4333,f4347,f4354,f4373,f4378,f4396,f4403,f4420,f4427,f4441,f4447,f4452,f4468,f4470,f4478,f4492,f4497,f4511,f4513,f4520,f4524,f4541,f4543,f4551,f4556,f4573,f4575,f4582,f4596,f4601,f4615,f4617,f4625,f4629,f4645,f4653,f4662,f4669,f4686,f4694,f4702,f4704,f4721,f4729,f4733,f4747,f4749,f4756,f4766,f4780,f4786,f4898,f4900,f4902,f5014,f5017,f5021,f5132,f5134,f5136,f5237,f5240,f5246,f5356,f5358,f5360,f5458,f5460,f5462,f5564,f5567,f5573,f5684,f5686,f5688,f5792,f5795,f5801,f5857,f5863,f5866,f6050,f6052,f6054,f6150,f6153,f6157,f6247,f6249,f6251,f6407,f6492,f6495,f6499,f6593,f6595,f6597])).

fof(f6597,plain,
    ( spl15_31
    | ~ spl15_40 ),
    inference(avatar_contradiction_clause,[],[f6596])).

fof(f6596,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_40 ),
    inference(subsumption_resolution,[],[f6509,f289])).

fof(f289,plain,(
    ! [X14,X12,X10,X19,X17,X15,X13,X11,X18,X16] : k8_enumset1(X11,X12,X13,X14,X15,X16,X17,X18,X10,X19) = k2_xboole_0(k1_tarski(X10),k8_enumset1(X11,X12,X13,X14,X15,X16,X17,X18,X10,X19)) ),
    inference(resolution,[],[f281,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X11,X9)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X11,X9) != X10 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ( X9 = X11
            | X8 = X11
            | X7 = X11
            | X6 = X11
            | X5 = X11
            | X4 = X11
            | X3 = X11
            | X2 = X11
            | X1 = X11
            | X0 = X11 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X9 != X11
              & X8 != X11
              & X7 != X11
              & X6 != X11
              & X5 != X11
              & X4 != X11
              & X3 != X11
              & X2 != X11
              & X1 != X11
              & X0 != X11 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',d8_enumset1)).

fof(f281,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | k2_xboole_0(k1_tarski(X8),X9) = X9 ) ),
    inference(subsumption_resolution,[],[f276,f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f235,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',d3_xboole_0)).

fof(f235,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1,X1),X1)
      | r2_hidden(sK12(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X2)
      | r2_hidden(sK12(X0,X1,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f276,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | ~ r2_hidden(sK12(k1_tarski(X8),X9,X9),k1_tarski(X8))
      | k2_xboole_0(k1_tarski(X8),X9) = X9 ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | ~ r2_hidden(sK12(k1_tarski(X8),X9,X9),k1_tarski(X8))
      | k2_xboole_0(k1_tarski(X8),X9) = X9
      | k2_xboole_0(k1_tarski(X8),X9) = X9 ) ),
    inference(superposition,[],[f63,f245])).

fof(f245,plain,(
    ! [X2,X3] :
      ( sK12(k1_tarski(X2),X3,X3) = X2
      | k2_xboole_0(k1_tarski(X2),X3) = X3 ) ),
    inference(resolution,[],[f240,f120])).

fof(f120,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',d1_tarski)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(X0,X1,X2),X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6509,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK8),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_40 ),
    inference(backward_demodulation,[],[f3774,f3182])).

fof(f3182,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31 ),
    inference(avatar_component_clause,[],[f3181])).

fof(f3181,plain,
    ( spl15_31
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_31])])).

fof(f3774,plain,
    ( sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_40 ),
    inference(avatar_component_clause,[],[f3773])).

fof(f3773,plain,
    ( spl15_40
  <=> sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f6595,plain,
    ( spl15_29
    | ~ spl15_40 ),
    inference(avatar_contradiction_clause,[],[f6594])).

fof(f6594,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_40 ),
    inference(subsumption_resolution,[],[f6508,f368])).

fof(f368,plain,(
    ! [X14,X12,X10,X19,X17,X15,X13,X11,X18,X16] : k8_enumset1(X10,X11,X12,X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k8_enumset1(X10,X11,X12,X13,X14,X15,X16,X17,X18,X19),k1_tarski(X18)) ),
    inference(resolution,[],[f360,f80])).

fof(f360,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X6)
      | k2_xboole_0(X6,k1_tarski(X7)) = X6 ) ),
    inference(subsumption_resolution,[],[f356,f241])).

fof(f241,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK12(X2,X3,X2),X3)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f236,f63])).

fof(f236,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK12(X2,X3,X2),X2)
      | r2_hidden(sK12(X2,X3,X2),X3)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(factoring,[],[f65])).

fof(f356,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X6)
      | ~ r2_hidden(sK12(X6,k1_tarski(X7),X6),k1_tarski(X7))
      | k2_xboole_0(X6,k1_tarski(X7)) = X6 ) ),
    inference(duplicate_literal_removal,[],[f349])).

fof(f349,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X6)
      | ~ r2_hidden(sK12(X6,k1_tarski(X7),X6),k1_tarski(X7))
      | k2_xboole_0(X6,k1_tarski(X7)) = X6
      | k2_xboole_0(X6,k1_tarski(X7)) = X6 ) ),
    inference(superposition,[],[f64,f257])).

fof(f257,plain,(
    ! [X2,X3] :
      ( sK12(X2,k1_tarski(X3),X2) = X3
      | k2_xboole_0(X2,k1_tarski(X3)) = X2 ) ),
    inference(resolution,[],[f241,f120])).

fof(f6508,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK8))
    | ~ spl15_29
    | ~ spl15_40 ),
    inference(backward_demodulation,[],[f3774,f3088])).

fof(f3088,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))))
    | ~ spl15_29 ),
    inference(avatar_component_clause,[],[f3087])).

fof(f3087,plain,
    ( spl15_29
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_29])])).

fof(f6593,plain,
    ( spl15_9
    | ~ spl15_40 ),
    inference(avatar_contradiction_clause,[],[f6592])).

fof(f6592,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_40 ),
    inference(subsumption_resolution,[],[f6504,f80])).

fof(f6504,plain,
    ( ~ r2_hidden(sK8,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_40 ),
    inference(backward_demodulation,[],[f3774,f207])).

fof(f207,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl15_9
  <=> ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f6499,plain,
    ( spl15_9
    | ~ spl15_52 ),
    inference(avatar_contradiction_clause,[],[f6498])).

fof(f6498,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f6497,f92])).

fof(f92,plain,(
    ! [X6,X4,X0,X8,X7,X5,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X11,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X11,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X2 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6497,plain,
    ( ~ r2_hidden(sK2,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f207,f3810])).

fof(f3810,plain,
    ( sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_52 ),
    inference(avatar_component_clause,[],[f3809])).

fof(f3809,plain,
    ( spl15_52
  <=> sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f6495,plain,
    ( spl15_29
    | ~ spl15_52 ),
    inference(avatar_contradiction_clause,[],[f6494])).

fof(f6494,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f6493,f374])).

fof(f374,plain,(
    ! [X70,X78,X76,X74,X72,X71,X79,X77,X75,X73] : k8_enumset1(X70,X71,X72,X73,X74,X75,X76,X77,X78,X79) = k2_xboole_0(k8_enumset1(X70,X71,X72,X73,X74,X75,X76,X77,X78,X79),k1_tarski(X72)) ),
    inference(resolution,[],[f360,f92])).

fof(f6493,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK2))
    | ~ spl15_29
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f3088,f3810])).

fof(f6492,plain,
    ( spl15_31
    | ~ spl15_52 ),
    inference(avatar_contradiction_clause,[],[f6491])).

fof(f6491,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f6490,f295])).

fof(f295,plain,(
    ! [X70,X78,X76,X74,X72,X71,X79,X77,X75,X73] : k8_enumset1(X71,X72,X70,X73,X74,X75,X76,X77,X78,X79) = k2_xboole_0(k1_tarski(X70),k8_enumset1(X71,X72,X70,X73,X74,X75,X76,X77,X78,X79)) ),
    inference(resolution,[],[f281,f92])).

fof(f6490,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK2),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f3182,f3810])).

fof(f6407,plain,
    ( spl15_17
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(avatar_contradiction_clause,[],[f6406])).

fof(f6406,plain,
    ( $false
    | ~ spl15_17
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f6405,f122])).

fof(f122,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f6405,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ spl15_17
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f6404,f6396])).

fof(f6396,plain,
    ( sK2 = sK14(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK2))
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f6281,f304])).

fof(f304,plain,(
    ! [X158,X156,X154,X161,X159,X157,X155,X162,X160] : k7_enumset1(X155,X156,X154,X157,X158,X159,X160,X161,X162) = k2_xboole_0(k1_tarski(X154),k7_enumset1(X155,X156,X154,X157,X158,X159,X160,X161,X162)) ),
    inference(resolution,[],[f281,f111])).

fof(f111,plain,(
    ! [X6,X4,X0,X10,X8,X7,X5,X3,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X10,X3,X4,X5,X6,X7,X8)) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X6,X4,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X10,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X2 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',d7_enumset1)).

fof(f6281,plain,
    ( sK2 = sK14(k2_xboole_0(k1_tarski(sK2),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK2))
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(backward_demodulation,[],[f6259,f3810])).

fof(f6259,plain,
    ( sK2 = sK9
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(backward_demodulation,[],[f3810,f3768])).

fof(f3768,plain,
    ( sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_38 ),
    inference(avatar_component_clause,[],[f3767])).

fof(f3767,plain,
    ( spl15_38
  <=> sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f6404,plain,
    ( ~ r2_hidden(sK14(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK2)),k1_tarski(sK2))
    | ~ spl15_17
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f6403,f304])).

fof(f6403,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK2),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK2)),k1_tarski(sK2))
    | ~ spl15_17
    | ~ spl15_38
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f591,f6259])).

fof(f591,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k1_tarski(sK9))
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl15_17
  <=> ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k1_tarski(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f6251,plain,
    ( spl15_31
    | ~ spl15_38 ),
    inference(avatar_contradiction_clause,[],[f6250])).

fof(f6250,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f6165,f288])).

fof(f288,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X0) = k2_xboole_0(k1_tarski(X0),k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X0)) ),
    inference(resolution,[],[f281,f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X11)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X11) != X10 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X9 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6165,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK9),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_38 ),
    inference(backward_demodulation,[],[f3768,f3182])).

fof(f6249,plain,
    ( spl15_29
    | ~ spl15_38 ),
    inference(avatar_contradiction_clause,[],[f6248])).

fof(f6248,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f6164,f367])).

fof(f367,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X9)) ),
    inference(resolution,[],[f360,f78])).

fof(f6164,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK9))
    | ~ spl15_29
    | ~ spl15_38 ),
    inference(backward_demodulation,[],[f3768,f3088])).

fof(f6247,plain,
    ( spl15_9
    | ~ spl15_38 ),
    inference(avatar_contradiction_clause,[],[f6246])).

fof(f6246,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f6162,f78])).

fof(f6162,plain,
    ( ~ r2_hidden(sK9,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_38 ),
    inference(backward_demodulation,[],[f3768,f207])).

fof(f6157,plain,
    ( spl15_9
    | ~ spl15_16 ),
    inference(avatar_contradiction_clause,[],[f6156])).

fof(f6156,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f6155,f78])).

fof(f6155,plain,
    ( ~ r2_hidden(sK9,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_16 ),
    inference(forward_demodulation,[],[f207,f4781])).

fof(f4781,plain,
    ( sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_16 ),
    inference(resolution,[],[f594,f120])).

fof(f594,plain,
    ( r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k1_tarski(sK9))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl15_16
  <=> r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k1_tarski(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f6153,plain,
    ( ~ spl15_16
    | spl15_29 ),
    inference(avatar_contradiction_clause,[],[f6152])).

fof(f6152,plain,
    ( $false
    | ~ spl15_16
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f6151,f367])).

fof(f6151,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK9))
    | ~ spl15_16
    | ~ spl15_29 ),
    inference(forward_demodulation,[],[f3088,f4781])).

fof(f6150,plain,
    ( ~ spl15_16
    | spl15_31 ),
    inference(avatar_contradiction_clause,[],[f6149])).

fof(f6149,plain,
    ( $false
    | ~ spl15_16
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f6148,f288])).

fof(f6148,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK9),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_16
    | ~ spl15_31 ),
    inference(forward_demodulation,[],[f3182,f4781])).

fof(f6054,plain,
    ( spl15_31
    | spl15_69
    | spl15_71 ),
    inference(avatar_contradiction_clause,[],[f6053])).

fof(f6053,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(subsumption_resolution,[],[f5963,f288])).

fof(f5963,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK9),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(backward_demodulation,[],[f4331,f3182])).

fof(f4331,plain,
    ( sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(subsumption_resolution,[],[f4330,f4325])).

fof(f4325,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK9)
    | ~ spl15_71 ),
    inference(avatar_component_clause,[],[f4324])).

fof(f4324,plain,
    ( spl15_71
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_71])])).

fof(f4330,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK9)
    | sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_69 ),
    inference(resolution,[],[f4319,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(X0,X1),X1)
      | r2_hidden(sK14(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',t2_tarski)).

fof(f4319,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_69 ),
    inference(avatar_component_clause,[],[f4318])).

fof(f4318,plain,
    ( spl15_69
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_69])])).

fof(f6052,plain,
    ( spl15_29
    | spl15_69
    | spl15_71 ),
    inference(avatar_contradiction_clause,[],[f6051])).

fof(f6051,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(subsumption_resolution,[],[f5962,f367])).

fof(f5962,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK9))
    | ~ spl15_29
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(backward_demodulation,[],[f4331,f3088])).

fof(f6050,plain,
    ( spl15_9
    | spl15_69
    | spl15_71 ),
    inference(avatar_contradiction_clause,[],[f6049])).

fof(f6049,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(subsumption_resolution,[],[f5960,f78])).

fof(f5960,plain,
    ( ~ r2_hidden(sK9,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(backward_demodulation,[],[f4331,f207])).

fof(f5866,plain,
    ( spl15_31
    | ~ spl15_44 ),
    inference(avatar_contradiction_clause,[],[f5865])).

fof(f5865,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f5864,f291])).

fof(f291,plain,(
    ! [X30,X39,X37,X35,X33,X31,X38,X36,X34,X32] : k8_enumset1(X31,X32,X33,X34,X35,X36,X30,X37,X38,X39) = k2_xboole_0(k1_tarski(X30),k8_enumset1(X31,X32,X33,X34,X35,X36,X30,X37,X38,X39)) ),
    inference(resolution,[],[f281,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X4,X5,X11,X7,X8,X9)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X11,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X6 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5864,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK6),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_44 ),
    inference(forward_demodulation,[],[f3182,f3786])).

fof(f3786,plain,
    ( sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_44 ),
    inference(avatar_component_clause,[],[f3785])).

fof(f3785,plain,
    ( spl15_44
  <=> sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f5863,plain,
    ( spl15_29
    | ~ spl15_44 ),
    inference(avatar_contradiction_clause,[],[f5862])).

fof(f5862,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f5861,f370])).

fof(f370,plain,(
    ! [X30,X39,X37,X35,X33,X31,X38,X36,X34,X32] : k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) = k2_xboole_0(k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39),k1_tarski(X36)) ),
    inference(resolution,[],[f360,f84])).

fof(f5861,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK6))
    | ~ spl15_29
    | ~ spl15_44 ),
    inference(forward_demodulation,[],[f3088,f3786])).

fof(f5857,plain,
    ( spl15_9
    | ~ spl15_44 ),
    inference(avatar_contradiction_clause,[],[f5856])).

fof(f5856,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f5855,f84])).

fof(f5855,plain,
    ( ~ r2_hidden(sK6,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_44 ),
    inference(forward_demodulation,[],[f207,f3786])).

fof(f5801,plain,
    ( spl15_9
    | ~ spl15_36 ),
    inference(avatar_contradiction_clause,[],[f5800])).

fof(f5800,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_36 ),
    inference(subsumption_resolution,[],[f5799,f96])).

fof(f96,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X11,X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X11,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X0 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5799,plain,
    ( ~ r2_hidden(sK0,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_36 ),
    inference(forward_demodulation,[],[f207,f3762])).

fof(f3762,plain,
    ( sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f3761])).

fof(f3761,plain,
    ( spl15_36
  <=> sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f5795,plain,
    ( spl15_29
    | ~ spl15_36 ),
    inference(avatar_contradiction_clause,[],[f5794])).

fof(f5794,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_36 ),
    inference(subsumption_resolution,[],[f5793,f376])).

fof(f376,plain,(
    ! [X94,X92,X90,X99,X97,X95,X93,X91,X98,X96] : k8_enumset1(X90,X91,X92,X93,X94,X95,X96,X97,X98,X99) = k2_xboole_0(k8_enumset1(X90,X91,X92,X93,X94,X95,X96,X97,X98,X99),k1_tarski(X90)) ),
    inference(resolution,[],[f360,f96])).

fof(f5793,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK0))
    | ~ spl15_29
    | ~ spl15_36 ),
    inference(forward_demodulation,[],[f3088,f3762])).

fof(f5792,plain,
    ( spl15_31
    | ~ spl15_36 ),
    inference(avatar_contradiction_clause,[],[f5791])).

fof(f5791,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_36 ),
    inference(subsumption_resolution,[],[f5790,f297])).

fof(f297,plain,(
    ! [X94,X92,X90,X99,X97,X95,X93,X91,X98,X96] : k8_enumset1(X90,X91,X92,X93,X94,X95,X96,X97,X98,X99) = k2_xboole_0(k1_tarski(X90),k8_enumset1(X90,X91,X92,X93,X94,X95,X96,X97,X98,X99)) ),
    inference(resolution,[],[f281,f96])).

fof(f5790,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK0),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_36 ),
    inference(forward_demodulation,[],[f3182,f3762])).

fof(f5688,plain,
    ( ~ spl15_18
    | spl15_31
    | spl15_41
    | spl15_43
    | spl15_45
    | spl15_47
    | spl15_49
    | spl15_51
    | spl15_53
    | spl15_55 ),
    inference(avatar_contradiction_clause,[],[f5687])).

fof(f5687,plain,
    ( $false
    | ~ spl15_18
    | ~ spl15_31
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f5583,f297])).

fof(f5583,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK0),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_31
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(backward_demodulation,[],[f4778,f3182])).

fof(f4778,plain,
    ( sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4777,f3771])).

fof(f3771,plain,
    ( sK8 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_41 ),
    inference(avatar_component_clause,[],[f3770])).

fof(f3770,plain,
    ( spl15_41
  <=> sK8 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_41])])).

fof(f4777,plain,
    ( sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4776,f3777])).

fof(f3777,plain,
    ( sK7 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_43 ),
    inference(avatar_component_clause,[],[f3776])).

fof(f3776,plain,
    ( spl15_43
  <=> sK7 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).

fof(f4776,plain,
    ( sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4775,f3783])).

fof(f3783,plain,
    ( sK6 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_45 ),
    inference(avatar_component_clause,[],[f3782])).

fof(f3782,plain,
    ( spl15_45
  <=> sK6 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).

fof(f4775,plain,
    ( sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4774,f3789])).

fof(f3789,plain,
    ( sK5 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_47 ),
    inference(avatar_component_clause,[],[f3788])).

fof(f3788,plain,
    ( spl15_47
  <=> sK5 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_47])])).

fof(f4774,plain,
    ( sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4773,f3795])).

fof(f3795,plain,
    ( sK4 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_49 ),
    inference(avatar_component_clause,[],[f3794])).

fof(f3794,plain,
    ( spl15_49
  <=> sK4 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_49])])).

fof(f4773,plain,
    ( sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4772,f3801])).

fof(f3801,plain,
    ( sK3 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_51 ),
    inference(avatar_component_clause,[],[f3800])).

fof(f3800,plain,
    ( spl15_51
  <=> sK3 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).

fof(f4772,plain,
    ( sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4771,f3807])).

fof(f3807,plain,
    ( sK2 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_53 ),
    inference(avatar_component_clause,[],[f3806])).

fof(f3806,plain,
    ( spl15_53
  <=> sK2 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).

fof(f4771,plain,
    ( sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4767,f3813])).

fof(f3813,plain,
    ( sK1 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_55 ),
    inference(avatar_component_clause,[],[f3812])).

fof(f3812,plain,
    ( spl15_55
  <=> sK1 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_55])])).

fof(f4767,plain,
    ( sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_18 ),
    inference(resolution,[],[f600,f116])).

fof(f116,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(X10,k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8))
      | X1 = X10
      | X2 = X10
      | X3 = X10
      | X4 = X10
      | X5 = X10
      | X6 = X10
      | X7 = X10
      | X8 = X10
      | X0 = X10 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X0 = X10
      | X1 = X10
      | X2 = X10
      | X3 = X10
      | X4 = X10
      | X5 = X10
      | X6 = X10
      | X7 = X10
      | X8 = X10
      | ~ r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f600,plain,
    ( r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl15_18
  <=> r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f5686,plain,
    ( ~ spl15_18
    | spl15_29
    | spl15_41
    | spl15_43
    | spl15_45
    | spl15_47
    | spl15_49
    | spl15_51
    | spl15_53
    | spl15_55 ),
    inference(avatar_contradiction_clause,[],[f5685])).

fof(f5685,plain,
    ( $false
    | ~ spl15_18
    | ~ spl15_29
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f5582,f376])).

fof(f5582,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK0))
    | ~ spl15_18
    | ~ spl15_29
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(backward_demodulation,[],[f4778,f3088])).

fof(f5684,plain,
    ( spl15_9
    | ~ spl15_18
    | spl15_41
    | spl15_43
    | spl15_45
    | spl15_47
    | spl15_49
    | spl15_51
    | spl15_53
    | spl15_55 ),
    inference(avatar_contradiction_clause,[],[f5683])).

fof(f5683,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_18
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f5578,f96])).

fof(f5578,plain,
    ( ~ r2_hidden(sK0,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_18
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(backward_demodulation,[],[f4778,f207])).

fof(f5573,plain,
    ( spl15_9
    | ~ spl15_46 ),
    inference(avatar_contradiction_clause,[],[f5572])).

fof(f5572,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f5571,f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X4,X11,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X11,X6,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X5 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5571,plain,
    ( ~ r2_hidden(sK5,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_46 ),
    inference(forward_demodulation,[],[f207,f3792])).

fof(f3792,plain,
    ( sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_46 ),
    inference(avatar_component_clause,[],[f3791])).

fof(f3791,plain,
    ( spl15_46
  <=> sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).

fof(f5567,plain,
    ( spl15_29
    | ~ spl15_46 ),
    inference(avatar_contradiction_clause,[],[f5566])).

fof(f5566,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f5565,f371])).

fof(f371,plain,(
    ! [X47,X45,X43,X41,X48,X46,X44,X42,X40,X49] : k8_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = k2_xboole_0(k8_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),k1_tarski(X45)) ),
    inference(resolution,[],[f360,f86])).

fof(f5565,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK5))
    | ~ spl15_29
    | ~ spl15_46 ),
    inference(forward_demodulation,[],[f3088,f3792])).

fof(f5564,plain,
    ( spl15_31
    | ~ spl15_46 ),
    inference(avatar_contradiction_clause,[],[f5563])).

fof(f5563,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f5562,f292])).

fof(f292,plain,(
    ! [X47,X45,X43,X41,X48,X46,X44,X42,X40,X49] : k8_enumset1(X41,X42,X43,X44,X45,X40,X46,X47,X48,X49) = k2_xboole_0(k1_tarski(X40),k8_enumset1(X41,X42,X43,X44,X45,X40,X46,X47,X48,X49)) ),
    inference(resolution,[],[f281,f86])).

fof(f5562,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK5),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_46 ),
    inference(forward_demodulation,[],[f3182,f3792])).

fof(f5462,plain,
    ( spl15_31
    | spl15_101
    | spl15_103 ),
    inference(avatar_contradiction_clause,[],[f5461])).

fof(f5461,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(subsumption_resolution,[],[f5366,f292])).

fof(f5366,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK5),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(backward_demodulation,[],[f4518,f3182])).

fof(f4518,plain,
    ( sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(subsumption_resolution,[],[f4517,f4510])).

fof(f4510,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK5)
    | ~ spl15_103 ),
    inference(avatar_component_clause,[],[f4509])).

fof(f4509,plain,
    ( spl15_103
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_103])])).

fof(f4517,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK5)
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_101 ),
    inference(resolution,[],[f4504,f73])).

fof(f4504,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_101 ),
    inference(avatar_component_clause,[],[f4503])).

fof(f4503,plain,
    ( spl15_101
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_101])])).

fof(f5460,plain,
    ( spl15_29
    | spl15_101
    | spl15_103 ),
    inference(avatar_contradiction_clause,[],[f5459])).

fof(f5459,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(subsumption_resolution,[],[f5365,f371])).

fof(f5365,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK5))
    | ~ spl15_29
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(backward_demodulation,[],[f4518,f3088])).

fof(f5458,plain,
    ( spl15_9
    | spl15_101
    | spl15_103 ),
    inference(avatar_contradiction_clause,[],[f5457])).

fof(f5457,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(subsumption_resolution,[],[f5361,f86])).

fof(f5361,plain,
    ( ~ r2_hidden(sK5,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(backward_demodulation,[],[f4518,f207])).

fof(f5360,plain,
    ( spl15_31
    | ~ spl15_42 ),
    inference(avatar_contradiction_clause,[],[f5359])).

fof(f5359,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f5256,f290])).

fof(f290,plain,(
    ! [X28,X26,X24,X23,X21,X29,X27,X25,X22,X20] : k8_enumset1(X21,X22,X23,X24,X25,X26,X27,X20,X28,X29) = k2_xboole_0(k1_tarski(X20),k8_enumset1(X21,X22,X23,X24,X25,X26,X27,X20,X28,X29)) ),
    inference(resolution,[],[f281,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X11,X8,X9)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X10,X8,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X11,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X7 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5256,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK7),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_42 ),
    inference(backward_demodulation,[],[f3780,f3182])).

fof(f3780,plain,
    ( sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_42 ),
    inference(avatar_component_clause,[],[f3779])).

fof(f3779,plain,
    ( spl15_42
  <=> sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).

fof(f5358,plain,
    ( spl15_29
    | ~ spl15_42 ),
    inference(avatar_contradiction_clause,[],[f5357])).

fof(f5357,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f5255,f369])).

fof(f369,plain,(
    ! [X28,X26,X24,X23,X21,X29,X27,X25,X22,X20] : k8_enumset1(X20,X21,X22,X23,X24,X25,X26,X27,X28,X29) = k2_xboole_0(k8_enumset1(X20,X21,X22,X23,X24,X25,X26,X27,X28,X29),k1_tarski(X27)) ),
    inference(resolution,[],[f360,f82])).

fof(f5255,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK7))
    | ~ spl15_29
    | ~ spl15_42 ),
    inference(backward_demodulation,[],[f3780,f3088])).

fof(f5356,plain,
    ( spl15_9
    | ~ spl15_42 ),
    inference(avatar_contradiction_clause,[],[f5355])).

fof(f5355,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f5251,f82])).

fof(f5251,plain,
    ( ~ r2_hidden(sK7,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_42 ),
    inference(backward_demodulation,[],[f3780,f207])).

fof(f5246,plain,
    ( spl15_9
    | ~ spl15_48 ),
    inference(avatar_contradiction_clause,[],[f5245])).

fof(f5245,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_48 ),
    inference(subsumption_resolution,[],[f5244,f88])).

fof(f88,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X11,X5,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X11,X5,X6,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X4 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5244,plain,
    ( ~ r2_hidden(sK4,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_48 ),
    inference(forward_demodulation,[],[f207,f3798])).

fof(f3798,plain,
    ( sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_48 ),
    inference(avatar_component_clause,[],[f3797])).

fof(f3797,plain,
    ( spl15_48
  <=> sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).

fof(f5240,plain,
    ( spl15_29
    | ~ spl15_48 ),
    inference(avatar_contradiction_clause,[],[f5239])).

fof(f5239,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_48 ),
    inference(subsumption_resolution,[],[f5238,f372])).

fof(f372,plain,(
    ! [X59,X57,X54,X52,X50,X58,X56,X55,X53,X51] : k8_enumset1(X50,X51,X52,X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k8_enumset1(X50,X51,X52,X53,X54,X55,X56,X57,X58,X59),k1_tarski(X54)) ),
    inference(resolution,[],[f360,f88])).

fof(f5238,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK4))
    | ~ spl15_29
    | ~ spl15_48 ),
    inference(forward_demodulation,[],[f3088,f3798])).

fof(f5237,plain,
    ( spl15_31
    | ~ spl15_48 ),
    inference(avatar_contradiction_clause,[],[f5236])).

fof(f5236,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_48 ),
    inference(subsumption_resolution,[],[f5235,f293])).

fof(f293,plain,(
    ! [X59,X57,X54,X52,X50,X58,X56,X55,X53,X51] : k8_enumset1(X51,X52,X53,X54,X50,X55,X56,X57,X58,X59) = k2_xboole_0(k1_tarski(X50),k8_enumset1(X51,X52,X53,X54,X50,X55,X56,X57,X58,X59)) ),
    inference(resolution,[],[f281,f88])).

fof(f5235,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK4),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_48 ),
    inference(forward_demodulation,[],[f3182,f3798])).

fof(f5136,plain,
    ( spl15_31
    | spl15_109
    | spl15_111 ),
    inference(avatar_contradiction_clause,[],[f5135])).

fof(f5135,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(subsumption_resolution,[],[f5031,f293])).

fof(f5031,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK4),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(backward_demodulation,[],[f4580,f3182])).

fof(f4580,plain,
    ( sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(subsumption_resolution,[],[f4579,f4572])).

fof(f4572,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK4)
    | ~ spl15_111 ),
    inference(avatar_component_clause,[],[f4571])).

fof(f4571,plain,
    ( spl15_111
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_111])])).

fof(f4579,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK4)
    | sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_109 ),
    inference(resolution,[],[f4566,f73])).

fof(f4566,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_109 ),
    inference(avatar_component_clause,[],[f4565])).

fof(f4565,plain,
    ( spl15_109
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_109])])).

fof(f5134,plain,
    ( spl15_29
    | spl15_109
    | spl15_111 ),
    inference(avatar_contradiction_clause,[],[f5133])).

fof(f5133,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(subsumption_resolution,[],[f5030,f372])).

fof(f5030,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK4))
    | ~ spl15_29
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(backward_demodulation,[],[f4580,f3088])).

fof(f5132,plain,
    ( spl15_9
    | spl15_109
    | spl15_111 ),
    inference(avatar_contradiction_clause,[],[f5131])).

fof(f5131,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(subsumption_resolution,[],[f5026,f88])).

fof(f5026,plain,
    ( ~ r2_hidden(sK4,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(backward_demodulation,[],[f4580,f207])).

fof(f5021,plain,
    ( spl15_9
    | ~ spl15_50 ),
    inference(avatar_contradiction_clause,[],[f5020])).

fof(f5020,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_50 ),
    inference(subsumption_resolution,[],[f5019,f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X1,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X1,X2,X11,X4,X5,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X1,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X11,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X3 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5019,plain,
    ( ~ r2_hidden(sK3,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_50 ),
    inference(forward_demodulation,[],[f207,f3804])).

fof(f3804,plain,
    ( sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_50 ),
    inference(avatar_component_clause,[],[f3803])).

fof(f3803,plain,
    ( spl15_50
  <=> sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_50])])).

fof(f5017,plain,
    ( spl15_29
    | ~ spl15_50 ),
    inference(avatar_contradiction_clause,[],[f5016])).

fof(f5016,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_50 ),
    inference(subsumption_resolution,[],[f5015,f373])).

fof(f373,plain,(
    ! [X61,X68,X66,X64,X62,X60,X69,X67,X65,X63] : k8_enumset1(X60,X61,X62,X63,X64,X65,X66,X67,X68,X69) = k2_xboole_0(k8_enumset1(X60,X61,X62,X63,X64,X65,X66,X67,X68,X69),k1_tarski(X63)) ),
    inference(resolution,[],[f360,f90])).

fof(f5015,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK3))
    | ~ spl15_29
    | ~ spl15_50 ),
    inference(forward_demodulation,[],[f3088,f3804])).

fof(f5014,plain,
    ( spl15_31
    | ~ spl15_50 ),
    inference(avatar_contradiction_clause,[],[f5013])).

fof(f5013,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_50 ),
    inference(subsumption_resolution,[],[f5012,f294])).

fof(f294,plain,(
    ! [X61,X68,X66,X64,X62,X60,X69,X67,X65,X63] : k8_enumset1(X61,X62,X63,X60,X64,X65,X66,X67,X68,X69) = k2_xboole_0(k1_tarski(X60),k8_enumset1(X61,X62,X63,X60,X64,X65,X66,X67,X68,X69)) ),
    inference(resolution,[],[f281,f90])).

fof(f5012,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK3),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_50 ),
    inference(forward_demodulation,[],[f3182,f3804])).

fof(f4902,plain,
    ( spl15_31
    | spl15_117
    | spl15_119 ),
    inference(avatar_contradiction_clause,[],[f4901])).

fof(f4901,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(subsumption_resolution,[],[f4790,f294])).

fof(f4790,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK3),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_31
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(backward_demodulation,[],[f4623,f3182])).

fof(f4623,plain,
    ( sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(subsumption_resolution,[],[f4622,f4614])).

fof(f4614,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK3)
    | ~ spl15_119 ),
    inference(avatar_component_clause,[],[f4613])).

fof(f4613,plain,
    ( spl15_119
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_119])])).

fof(f4622,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK3)
    | sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_117 ),
    inference(resolution,[],[f4608,f73])).

fof(f4608,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_117 ),
    inference(avatar_component_clause,[],[f4607])).

fof(f4607,plain,
    ( spl15_117
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_117])])).

fof(f4900,plain,
    ( spl15_29
    | spl15_117
    | spl15_119 ),
    inference(avatar_contradiction_clause,[],[f4899])).

fof(f4899,plain,
    ( $false
    | ~ spl15_29
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(subsumption_resolution,[],[f4789,f373])).

fof(f4789,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK3))
    | ~ spl15_29
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(backward_demodulation,[],[f4623,f3088])).

fof(f4898,plain,
    ( spl15_9
    | spl15_117
    | spl15_119 ),
    inference(avatar_contradiction_clause,[],[f4897])).

fof(f4897,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(subsumption_resolution,[],[f4787,f90])).

fof(f4787,plain,
    ( ~ r2_hidden(sK3,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(backward_demodulation,[],[f4623,f207])).

fof(f4786,plain,
    ( ~ spl15_16
    | spl15_39 ),
    inference(avatar_contradiction_clause,[],[f4785])).

fof(f4785,plain,
    ( $false
    | ~ spl15_16
    | ~ spl15_39 ),
    inference(subsumption_resolution,[],[f4781,f3765])).

fof(f3765,plain,
    ( sK9 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_39 ),
    inference(avatar_component_clause,[],[f3764])).

fof(f3764,plain,
    ( spl15_39
  <=> sK9 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_39])])).

fof(f4780,plain,
    ( ~ spl15_18
    | spl15_37
    | spl15_41
    | spl15_43
    | spl15_45
    | spl15_47
    | spl15_49
    | spl15_51
    | spl15_53
    | spl15_55 ),
    inference(avatar_contradiction_clause,[],[f4779])).

fof(f4779,plain,
    ( $false
    | ~ spl15_18
    | ~ spl15_37
    | ~ spl15_41
    | ~ spl15_43
    | ~ spl15_45
    | ~ spl15_47
    | ~ spl15_49
    | ~ spl15_51
    | ~ spl15_53
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f4778,f3759])).

fof(f3759,plain,
    ( sK0 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_37 ),
    inference(avatar_component_clause,[],[f3758])).

fof(f3758,plain,
    ( spl15_37
  <=> sK0 != sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).

fof(f4766,plain,
    ( spl15_144
    | ~ spl15_64 ),
    inference(avatar_split_clause,[],[f4516,f4294,f4764])).

fof(f4764,plain,
    ( spl15_144
  <=> k2_xboole_0(k1_tarski(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))),sK9) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_144])])).

fof(f4294,plain,
    ( spl15_64
  <=> r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f4516,plain,
    ( k2_xboole_0(k1_tarski(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))),sK9) = sK9
    | ~ spl15_64 ),
    inference(resolution,[],[f4295,f281])).

fof(f4295,plain,
    ( r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9)
    | ~ spl15_64 ),
    inference(avatar_component_clause,[],[f4294])).

fof(f4756,plain,
    ( spl15_55
    | spl15_141
    | spl15_143 ),
    inference(avatar_contradiction_clause,[],[f4755])).

fof(f4755,plain,
    ( $false
    | ~ spl15_55
    | ~ spl15_141
    | ~ spl15_143 ),
    inference(subsumption_resolution,[],[f4754,f3813])).

fof(f4754,plain,
    ( sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_141
    | ~ spl15_143 ),
    inference(subsumption_resolution,[],[f4753,f4746])).

fof(f4746,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK1)
    | ~ spl15_143 ),
    inference(avatar_component_clause,[],[f4745])).

fof(f4745,plain,
    ( spl15_143
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_143])])).

fof(f4753,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK1)
    | sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_141 ),
    inference(resolution,[],[f4740,f73])).

fof(f4740,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_141 ),
    inference(avatar_component_clause,[],[f4739])).

fof(f4739,plain,
    ( spl15_141
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_141])])).

fof(f4749,plain,
    ( spl15_134
    | spl15_55
    | spl15_137 ),
    inference(avatar_split_clause,[],[f4734,f4719,f3812,f4710])).

fof(f4710,plain,
    ( spl15_134
  <=> r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_134])])).

fof(f4719,plain,
    ( spl15_137
  <=> ~ r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_137])])).

fof(f4734,plain,
    ( r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK1)
    | ~ spl15_55
    | ~ spl15_137 ),
    inference(subsumption_resolution,[],[f4730,f3813])).

fof(f4730,plain,
    ( r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK1)
    | sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_137 ),
    inference(resolution,[],[f4720,f73])).

fof(f4720,plain,
    ( ~ r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_137 ),
    inference(avatar_component_clause,[],[f4719])).

fof(f4747,plain,
    ( ~ spl15_141
    | ~ spl15_143
    | spl15_55 ),
    inference(avatar_split_clause,[],[f4422,f3812,f4745,f4739])).

fof(f4422,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK1)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK1),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_55 ),
    inference(extensionality_resolution,[],[f74,f3813])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK14(X0,X1),X1)
      | ~ r2_hidden(sK14(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4733,plain,
    ( spl15_55
    | spl15_135
    | spl15_137 ),
    inference(avatar_contradiction_clause,[],[f4732])).

fof(f4732,plain,
    ( $false
    | ~ spl15_55
    | ~ spl15_135
    | ~ spl15_137 ),
    inference(subsumption_resolution,[],[f4731,f3813])).

fof(f4731,plain,
    ( sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_135
    | ~ spl15_137 ),
    inference(subsumption_resolution,[],[f4730,f4714])).

fof(f4714,plain,
    ( ~ r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK1)
    | ~ spl15_135 ),
    inference(avatar_component_clause,[],[f4713])).

fof(f4713,plain,
    ( spl15_135
  <=> ~ r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_135])])).

fof(f4729,plain,
    ( spl15_138
    | ~ spl15_64 ),
    inference(avatar_split_clause,[],[f4515,f4294,f4727])).

fof(f4727,plain,
    ( spl15_138
  <=> k2_xboole_0(sK9,k1_tarski(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_138])])).

fof(f4515,plain,
    ( k2_xboole_0(sK9,k1_tarski(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))))) = sK9
    | ~ spl15_64 ),
    inference(resolution,[],[f4295,f360])).

fof(f4721,plain,
    ( ~ spl15_135
    | ~ spl15_137
    | spl15_55 ),
    inference(avatar_split_clause,[],[f4421,f3812,f4719,f4713])).

fof(f4421,plain,
    ( ~ r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK1,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK1)
    | ~ spl15_55 ),
    inference(extensionality_resolution,[],[f74,f3813])).

fof(f4704,plain,
    ( spl15_130
    | spl15_53
    | spl15_129 ),
    inference(avatar_split_clause,[],[f4703,f4678,f3806,f4681])).

fof(f4681,plain,
    ( spl15_130
  <=> r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_130])])).

fof(f4678,plain,
    ( spl15_129
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_129])])).

fof(f4703,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK2)
    | ~ spl15_53
    | ~ spl15_129 ),
    inference(subsumption_resolution,[],[f4699,f3807])).

fof(f4699,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK2)
    | sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_129 ),
    inference(resolution,[],[f4679,f73])).

fof(f4679,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_129 ),
    inference(avatar_component_clause,[],[f4678])).

fof(f4702,plain,
    ( spl15_53
    | spl15_129
    | spl15_131 ),
    inference(avatar_contradiction_clause,[],[f4701])).

fof(f4701,plain,
    ( $false
    | ~ spl15_53
    | ~ spl15_129
    | ~ spl15_131 ),
    inference(subsumption_resolution,[],[f4700,f3807])).

fof(f4700,plain,
    ( sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_129
    | ~ spl15_131 ),
    inference(subsumption_resolution,[],[f4699,f4685])).

fof(f4685,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK2)
    | ~ spl15_131 ),
    inference(avatar_component_clause,[],[f4684])).

fof(f4684,plain,
    ( spl15_131
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_131])])).

fof(f4694,plain,
    ( spl15_132
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f4474,f4279,f4692])).

fof(f4692,plain,
    ( spl15_132
  <=> k2_xboole_0(k1_tarski(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0)),sK0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_132])])).

fof(f4279,plain,
    ( spl15_62
  <=> r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_62])])).

fof(f4474,plain,
    ( k2_xboole_0(k1_tarski(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0)),sK0) = sK0
    | ~ spl15_62 ),
    inference(resolution,[],[f4280,f281])).

fof(f4280,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0)
    | ~ spl15_62 ),
    inference(avatar_component_clause,[],[f4279])).

fof(f4686,plain,
    ( ~ spl15_129
    | ~ spl15_131
    | spl15_53 ),
    inference(avatar_split_clause,[],[f4399,f3806,f4684,f4678])).

fof(f4399,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK2)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK2),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_53 ),
    inference(extensionality_resolution,[],[f74,f3807])).

fof(f4669,plain,
    ( spl15_126
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f4473,f4279,f4667])).

fof(f4667,plain,
    ( spl15_126
  <=> k2_xboole_0(sK0,k1_tarski(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0))) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_126])])).

fof(f4473,plain,
    ( k2_xboole_0(sK0,k1_tarski(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0))) = sK0
    | ~ spl15_62 ),
    inference(resolution,[],[f4280,f360])).

fof(f4662,plain,
    ( spl15_53
    | spl15_121
    | spl15_123 ),
    inference(avatar_contradiction_clause,[],[f4661])).

fof(f4661,plain,
    ( $false
    | ~ spl15_53
    | ~ spl15_121
    | ~ spl15_123 ),
    inference(subsumption_resolution,[],[f4660,f3807])).

fof(f4660,plain,
    ( sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_121
    | ~ spl15_123 ),
    inference(subsumption_resolution,[],[f4659,f4638])).

fof(f4638,plain,
    ( ~ r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK2)
    | ~ spl15_121 ),
    inference(avatar_component_clause,[],[f4637])).

fof(f4637,plain,
    ( spl15_121
  <=> ~ r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_121])])).

fof(f4659,plain,
    ( r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK2)
    | sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_123 ),
    inference(resolution,[],[f4644,f73])).

fof(f4644,plain,
    ( ~ r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_123 ),
    inference(avatar_component_clause,[],[f4643])).

fof(f4643,plain,
    ( spl15_123
  <=> ~ r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_123])])).

fof(f4653,plain,
    ( spl15_124
    | ~ spl15_56 ),
    inference(avatar_split_clause,[],[f4454,f4252,f4651])).

fof(f4651,plain,
    ( spl15_124
  <=> k2_xboole_0(sK0,k1_tarski(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))))) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_124])])).

fof(f4252,plain,
    ( spl15_56
  <=> r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_56])])).

fof(f4454,plain,
    ( k2_xboole_0(sK0,k1_tarski(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))))) = sK0
    | ~ spl15_56 ),
    inference(resolution,[],[f4253,f360])).

fof(f4253,plain,
    ( r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0)
    | ~ spl15_56 ),
    inference(avatar_component_clause,[],[f4252])).

fof(f4645,plain,
    ( ~ spl15_121
    | ~ spl15_123
    | spl15_53 ),
    inference(avatar_split_clause,[],[f4398,f3806,f4643,f4637])).

fof(f4398,plain,
    ( ~ r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK2,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK2)
    | ~ spl15_53 ),
    inference(extensionality_resolution,[],[f74,f3807])).

fof(f4629,plain,
    ( spl15_112
    | spl15_51
    | spl15_115 ),
    inference(avatar_split_clause,[],[f4602,f4594,f3800,f4585])).

fof(f4585,plain,
    ( spl15_112
  <=> r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_112])])).

fof(f4594,plain,
    ( spl15_115
  <=> ~ r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_115])])).

fof(f4602,plain,
    ( r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK3)
    | ~ spl15_51
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f4598,f3801])).

fof(f4598,plain,
    ( r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK3)
    | sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_115 ),
    inference(resolution,[],[f4595,f73])).

fof(f4595,plain,
    ( ~ r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_115 ),
    inference(avatar_component_clause,[],[f4594])).

fof(f4625,plain,
    ( spl15_51
    | spl15_117
    | spl15_119 ),
    inference(avatar_contradiction_clause,[],[f4624])).

fof(f4624,plain,
    ( $false
    | ~ spl15_51
    | ~ spl15_117
    | ~ spl15_119 ),
    inference(subsumption_resolution,[],[f4623,f3801])).

fof(f4617,plain,
    ( spl15_110
    | spl15_49
    | spl15_109 ),
    inference(avatar_split_clause,[],[f4583,f4565,f3794,f4568])).

fof(f4568,plain,
    ( spl15_110
  <=> r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_110])])).

fof(f4583,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK4)
    | ~ spl15_49
    | ~ spl15_109 ),
    inference(subsumption_resolution,[],[f4579,f3795])).

fof(f4615,plain,
    ( ~ spl15_117
    | ~ spl15_119
    | spl15_51 ),
    inference(avatar_split_clause,[],[f4380,f3800,f4613,f4607])).

fof(f4380,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK3)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK3),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_51 ),
    inference(extensionality_resolution,[],[f74,f3801])).

fof(f4601,plain,
    ( spl15_51
    | spl15_113
    | spl15_115 ),
    inference(avatar_contradiction_clause,[],[f4600])).

fof(f4600,plain,
    ( $false
    | ~ spl15_51
    | ~ spl15_113
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f4599,f3801])).

fof(f4599,plain,
    ( sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_113
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f4598,f4589])).

fof(f4589,plain,
    ( ~ r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK3)
    | ~ spl15_113 ),
    inference(avatar_component_clause,[],[f4588])).

fof(f4588,plain,
    ( spl15_113
  <=> ~ r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_113])])).

fof(f4596,plain,
    ( ~ spl15_113
    | ~ spl15_115
    | spl15_51 ),
    inference(avatar_split_clause,[],[f4379,f3800,f4594,f4588])).

fof(f4379,plain,
    ( ~ r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK3,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK3)
    | ~ spl15_51 ),
    inference(extensionality_resolution,[],[f74,f3801])).

fof(f4582,plain,
    ( spl15_49
    | spl15_109
    | spl15_111 ),
    inference(avatar_contradiction_clause,[],[f4581])).

fof(f4581,plain,
    ( $false
    | ~ spl15_49
    | ~ spl15_109
    | ~ spl15_111 ),
    inference(subsumption_resolution,[],[f4580,f3795])).

fof(f4575,plain,
    ( spl15_96
    | spl15_47
    | spl15_99 ),
    inference(avatar_split_clause,[],[f4498,f4490,f3788,f4481])).

fof(f4481,plain,
    ( spl15_96
  <=> r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).

fof(f4490,plain,
    ( spl15_99
  <=> ~ r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_99])])).

fof(f4498,plain,
    ( r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK5)
    | ~ spl15_47
    | ~ spl15_99 ),
    inference(subsumption_resolution,[],[f4494,f3789])).

fof(f4494,plain,
    ( r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK5)
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_99 ),
    inference(resolution,[],[f4491,f73])).

fof(f4491,plain,
    ( ~ r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_99 ),
    inference(avatar_component_clause,[],[f4490])).

fof(f4573,plain,
    ( ~ spl15_109
    | ~ spl15_111
    | spl15_49 ),
    inference(avatar_split_clause,[],[f4360,f3794,f4571,f4565])).

fof(f4360,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK4)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK4),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_49 ),
    inference(extensionality_resolution,[],[f74,f3795])).

fof(f4556,plain,
    ( spl15_94
    | spl15_45
    | spl15_93 ),
    inference(avatar_split_clause,[],[f4479,f4460,f3782,f4463])).

fof(f4463,plain,
    ( spl15_94
  <=> r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_94])])).

fof(f4460,plain,
    ( spl15_93
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_93])])).

fof(f4479,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK6)
    | ~ spl15_45
    | ~ spl15_93 ),
    inference(subsumption_resolution,[],[f4475,f3783])).

fof(f4475,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK6)
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_93 ),
    inference(resolution,[],[f4461,f73])).

fof(f4461,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_93 ),
    inference(avatar_component_clause,[],[f4460])).

fof(f4551,plain,
    ( spl15_49
    | spl15_105
    | spl15_107 ),
    inference(avatar_contradiction_clause,[],[f4550])).

fof(f4550,plain,
    ( $false
    | ~ spl15_49
    | ~ spl15_105
    | ~ spl15_107 ),
    inference(subsumption_resolution,[],[f4549,f3795])).

fof(f4549,plain,
    ( sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_105
    | ~ spl15_107 ),
    inference(subsumption_resolution,[],[f4548,f4534])).

fof(f4534,plain,
    ( ~ r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK4)
    | ~ spl15_105 ),
    inference(avatar_component_clause,[],[f4533])).

fof(f4533,plain,
    ( spl15_105
  <=> ~ r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_105])])).

fof(f4548,plain,
    ( r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK4)
    | sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_107 ),
    inference(resolution,[],[f4540,f73])).

fof(f4540,plain,
    ( ~ r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_107 ),
    inference(avatar_component_clause,[],[f4539])).

fof(f4539,plain,
    ( spl15_107
  <=> ~ r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_107])])).

fof(f4543,plain,
    ( spl15_86
    | spl15_43
    | spl15_85 ),
    inference(avatar_split_clause,[],[f4428,f4412,f3776,f4415])).

fof(f4415,plain,
    ( spl15_86
  <=> r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_86])])).

fof(f4412,plain,
    ( spl15_85
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_85])])).

fof(f4428,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK7)
    | ~ spl15_43
    | ~ spl15_85 ),
    inference(subsumption_resolution,[],[f4424,f3777])).

fof(f4424,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK7)
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_85 ),
    inference(resolution,[],[f4413,f73])).

fof(f4413,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_85 ),
    inference(avatar_component_clause,[],[f4412])).

fof(f4541,plain,
    ( ~ spl15_105
    | ~ spl15_107
    | spl15_49 ),
    inference(avatar_split_clause,[],[f4359,f3794,f4539,f4533])).

fof(f4359,plain,
    ( ~ r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK4,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK4)
    | ~ spl15_49 ),
    inference(extensionality_resolution,[],[f74,f3795])).

fof(f4524,plain,
    ( spl15_70
    | spl15_39
    | spl15_69 ),
    inference(avatar_split_clause,[],[f4334,f4318,f3764,f4321])).

fof(f4321,plain,
    ( spl15_70
  <=> r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).

fof(f4334,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK9)
    | ~ spl15_39
    | ~ spl15_69 ),
    inference(subsumption_resolution,[],[f4330,f3765])).

fof(f4520,plain,
    ( spl15_47
    | spl15_101
    | spl15_103 ),
    inference(avatar_contradiction_clause,[],[f4519])).

fof(f4519,plain,
    ( $false
    | ~ spl15_47
    | ~ spl15_101
    | ~ spl15_103 ),
    inference(subsumption_resolution,[],[f4518,f3789])).

fof(f4513,plain,
    ( spl15_64
    | spl15_39
    | spl15_67 ),
    inference(avatar_split_clause,[],[f4313,f4303,f3764,f4294])).

fof(f4303,plain,
    ( spl15_67
  <=> ~ r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_67])])).

fof(f4313,plain,
    ( r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9)
    | ~ spl15_39
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f4309,f3765])).

fof(f4309,plain,
    ( r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9)
    | sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_67 ),
    inference(resolution,[],[f4304,f73])).

fof(f4304,plain,
    ( ~ r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_67 ),
    inference(avatar_component_clause,[],[f4303])).

fof(f4511,plain,
    ( ~ spl15_101
    | ~ spl15_103
    | spl15_47 ),
    inference(avatar_split_clause,[],[f4349,f3788,f4509,f4503])).

fof(f4349,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK5)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK5),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_47 ),
    inference(extensionality_resolution,[],[f74,f3789])).

fof(f4497,plain,
    ( spl15_47
    | spl15_97
    | spl15_99 ),
    inference(avatar_contradiction_clause,[],[f4496])).

fof(f4496,plain,
    ( $false
    | ~ spl15_47
    | ~ spl15_97
    | ~ spl15_99 ),
    inference(subsumption_resolution,[],[f4495,f3789])).

fof(f4495,plain,
    ( sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_97
    | ~ spl15_99 ),
    inference(subsumption_resolution,[],[f4494,f4485])).

fof(f4485,plain,
    ( ~ r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK5)
    | ~ spl15_97 ),
    inference(avatar_component_clause,[],[f4484])).

fof(f4484,plain,
    ( spl15_97
  <=> ~ r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_97])])).

fof(f4492,plain,
    ( ~ spl15_97
    | ~ spl15_99
    | spl15_47 ),
    inference(avatar_split_clause,[],[f4348,f3788,f4490,f4484])).

fof(f4348,plain,
    ( ~ r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK5,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK5)
    | ~ spl15_47 ),
    inference(extensionality_resolution,[],[f74,f3789])).

fof(f4478,plain,
    ( spl15_45
    | spl15_93
    | spl15_95 ),
    inference(avatar_contradiction_clause,[],[f4477])).

fof(f4477,plain,
    ( $false
    | ~ spl15_45
    | ~ spl15_93
    | ~ spl15_95 ),
    inference(subsumption_resolution,[],[f4476,f3783])).

fof(f4476,plain,
    ( sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_93
    | ~ spl15_95 ),
    inference(subsumption_resolution,[],[f4475,f4467])).

fof(f4467,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK6)
    | ~ spl15_95 ),
    inference(avatar_component_clause,[],[f4466])).

fof(f4466,plain,
    ( spl15_95
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_95])])).

fof(f4470,plain,
    ( spl15_62
    | spl15_37
    | spl15_61 ),
    inference(avatar_split_clause,[],[f4292,f4276,f3758,f4279])).

fof(f4276,plain,
    ( spl15_61
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_61])])).

fof(f4292,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0)
    | ~ spl15_37
    | ~ spl15_61 ),
    inference(subsumption_resolution,[],[f4288,f3759])).

fof(f4288,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0)
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_61 ),
    inference(resolution,[],[f4277,f73])).

fof(f4277,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_61 ),
    inference(avatar_component_clause,[],[f4276])).

fof(f4468,plain,
    ( ~ spl15_93
    | ~ spl15_95
    | spl15_45 ),
    inference(avatar_split_clause,[],[f4328,f3782,f4466,f4460])).

fof(f4328,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK6)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK6),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_45 ),
    inference(extensionality_resolution,[],[f74,f3783])).

fof(f4452,plain,
    ( spl15_56
    | spl15_37
    | spl15_59 ),
    inference(avatar_split_clause,[],[f4271,f4261,f3758,f4252])).

fof(f4261,plain,
    ( spl15_59
  <=> ~ r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_59])])).

fof(f4271,plain,
    ( r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0)
    | ~ spl15_37
    | ~ spl15_59 ),
    inference(subsumption_resolution,[],[f4267,f3759])).

fof(f4267,plain,
    ( r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0)
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_59 ),
    inference(resolution,[],[f4262,f73])).

fof(f4262,plain,
    ( ~ r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_59 ),
    inference(avatar_component_clause,[],[f4261])).

fof(f4447,plain,
    ( spl15_45
    | spl15_89
    | spl15_91 ),
    inference(avatar_contradiction_clause,[],[f4446])).

fof(f4446,plain,
    ( $false
    | ~ spl15_45
    | ~ spl15_89
    | ~ spl15_91 ),
    inference(subsumption_resolution,[],[f4445,f3783])).

fof(f4445,plain,
    ( sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_89
    | ~ spl15_91 ),
    inference(subsumption_resolution,[],[f4444,f4434])).

fof(f4434,plain,
    ( ~ r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK6)
    | ~ spl15_89 ),
    inference(avatar_component_clause,[],[f4433])).

fof(f4433,plain,
    ( spl15_89
  <=> ~ r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_89])])).

fof(f4444,plain,
    ( r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK6)
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_91 ),
    inference(resolution,[],[f4440,f73])).

fof(f4440,plain,
    ( ~ r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_91 ),
    inference(avatar_component_clause,[],[f4439])).

fof(f4439,plain,
    ( spl15_91
  <=> ~ r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_91])])).

fof(f4441,plain,
    ( ~ spl15_89
    | ~ spl15_91
    | spl15_45 ),
    inference(avatar_split_clause,[],[f4327,f3782,f4439,f4433])).

fof(f4327,plain,
    ( ~ r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK6,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK6)
    | ~ spl15_45 ),
    inference(extensionality_resolution,[],[f74,f3783])).

fof(f4427,plain,
    ( spl15_43
    | spl15_85
    | spl15_87 ),
    inference(avatar_contradiction_clause,[],[f4426])).

fof(f4426,plain,
    ( $false
    | ~ spl15_43
    | ~ spl15_85
    | ~ spl15_87 ),
    inference(subsumption_resolution,[],[f4425,f3777])).

fof(f4425,plain,
    ( sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_85
    | ~ spl15_87 ),
    inference(subsumption_resolution,[],[f4424,f4419])).

fof(f4419,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK7)
    | ~ spl15_87 ),
    inference(avatar_component_clause,[],[f4418])).

fof(f4418,plain,
    ( spl15_87
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_87])])).

fof(f4420,plain,
    ( ~ spl15_85
    | ~ spl15_87
    | spl15_43 ),
    inference(avatar_split_clause,[],[f4307,f3776,f4418,f4412])).

fof(f4307,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK7)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK7),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_43 ),
    inference(extensionality_resolution,[],[f74,f3777])).

fof(f4403,plain,
    ( spl15_43
    | spl15_81
    | spl15_83 ),
    inference(avatar_contradiction_clause,[],[f4402])).

fof(f4402,plain,
    ( $false
    | ~ spl15_43
    | ~ spl15_81
    | ~ spl15_83 ),
    inference(subsumption_resolution,[],[f4401,f3777])).

fof(f4401,plain,
    ( sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_81
    | ~ spl15_83 ),
    inference(subsumption_resolution,[],[f4400,f4389])).

fof(f4389,plain,
    ( ~ r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK7)
    | ~ spl15_81 ),
    inference(avatar_component_clause,[],[f4388])).

fof(f4388,plain,
    ( spl15_81
  <=> ~ r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_81])])).

fof(f4400,plain,
    ( r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK7)
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_83 ),
    inference(resolution,[],[f4395,f73])).

fof(f4395,plain,
    ( ~ r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_83 ),
    inference(avatar_component_clause,[],[f4394])).

fof(f4394,plain,
    ( spl15_83
  <=> ~ r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_83])])).

fof(f4396,plain,
    ( ~ spl15_81
    | ~ spl15_83
    | spl15_43 ),
    inference(avatar_split_clause,[],[f4306,f3776,f4394,f4388])).

fof(f4306,plain,
    ( ~ r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK7,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK7)
    | ~ spl15_43 ),
    inference(extensionality_resolution,[],[f74,f3777])).

fof(f4378,plain,
    ( spl15_41
    | spl15_77
    | spl15_79 ),
    inference(avatar_contradiction_clause,[],[f4377])).

fof(f4377,plain,
    ( $false
    | ~ spl15_41
    | ~ spl15_77
    | ~ spl15_79 ),
    inference(subsumption_resolution,[],[f4376,f3771])).

fof(f4376,plain,
    ( sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_77
    | ~ spl15_79 ),
    inference(subsumption_resolution,[],[f4375,f4372])).

fof(f4372,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK8)
    | ~ spl15_79 ),
    inference(avatar_component_clause,[],[f4371])).

fof(f4371,plain,
    ( spl15_79
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_79])])).

fof(f4375,plain,
    ( r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK8)
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_77 ),
    inference(resolution,[],[f4366,f73])).

fof(f4366,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_77 ),
    inference(avatar_component_clause,[],[f4365])).

fof(f4365,plain,
    ( spl15_77
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_77])])).

fof(f4373,plain,
    ( ~ spl15_77
    | ~ spl15_79
    | spl15_41 ),
    inference(avatar_split_clause,[],[f4286,f3770,f4371,f4365])).

fof(f4286,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK8)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK8),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_41 ),
    inference(extensionality_resolution,[],[f74,f3771])).

fof(f4354,plain,
    ( spl15_41
    | spl15_73
    | spl15_75 ),
    inference(avatar_contradiction_clause,[],[f4353])).

fof(f4353,plain,
    ( $false
    | ~ spl15_41
    | ~ spl15_73
    | ~ spl15_75 ),
    inference(subsumption_resolution,[],[f4352,f3771])).

fof(f4352,plain,
    ( sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_73
    | ~ spl15_75 ),
    inference(subsumption_resolution,[],[f4351,f4340])).

fof(f4340,plain,
    ( ~ r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK8)
    | ~ spl15_73 ),
    inference(avatar_component_clause,[],[f4339])).

fof(f4339,plain,
    ( spl15_73
  <=> ~ r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_73])])).

fof(f4351,plain,
    ( r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK8)
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_75 ),
    inference(resolution,[],[f4346,f73])).

fof(f4346,plain,
    ( ~ r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_75 ),
    inference(avatar_component_clause,[],[f4345])).

fof(f4345,plain,
    ( spl15_75
  <=> ~ r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_75])])).

fof(f4347,plain,
    ( ~ spl15_73
    | ~ spl15_75
    | spl15_41 ),
    inference(avatar_split_clause,[],[f4285,f3770,f4345,f4339])).

fof(f4285,plain,
    ( ~ r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK8,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK8)
    | ~ spl15_41 ),
    inference(extensionality_resolution,[],[f74,f3771])).

fof(f4333,plain,
    ( spl15_39
    | spl15_69
    | spl15_71 ),
    inference(avatar_contradiction_clause,[],[f4332])).

fof(f4332,plain,
    ( $false
    | ~ spl15_39
    | ~ spl15_69
    | ~ spl15_71 ),
    inference(subsumption_resolution,[],[f4331,f3765])).

fof(f4326,plain,
    ( ~ spl15_69
    | ~ spl15_71
    | spl15_39 ),
    inference(avatar_split_clause,[],[f4265,f3764,f4324,f4318])).

fof(f4265,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK9)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK9),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_39 ),
    inference(extensionality_resolution,[],[f74,f3765])).

fof(f4312,plain,
    ( spl15_39
    | spl15_65
    | spl15_67 ),
    inference(avatar_contradiction_clause,[],[f4311])).

fof(f4311,plain,
    ( $false
    | ~ spl15_39
    | ~ spl15_65
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f4310,f3765])).

fof(f4310,plain,
    ( sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_65
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f4309,f4298])).

fof(f4298,plain,
    ( ~ r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9)
    | ~ spl15_65 ),
    inference(avatar_component_clause,[],[f4297])).

fof(f4297,plain,
    ( spl15_65
  <=> ~ r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_65])])).

fof(f4305,plain,
    ( ~ spl15_65
    | ~ spl15_67
    | spl15_39 ),
    inference(avatar_split_clause,[],[f4264,f3764,f4303,f4297])).

fof(f4264,plain,
    ( ~ r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK9,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK9)
    | ~ spl15_39 ),
    inference(extensionality_resolution,[],[f74,f3765])).

fof(f4291,plain,
    ( spl15_37
    | spl15_61
    | spl15_63 ),
    inference(avatar_contradiction_clause,[],[f4290])).

fof(f4290,plain,
    ( $false
    | ~ spl15_37
    | ~ spl15_61
    | ~ spl15_63 ),
    inference(subsumption_resolution,[],[f4289,f3759])).

fof(f4289,plain,
    ( sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_61
    | ~ spl15_63 ),
    inference(subsumption_resolution,[],[f4288,f4283])).

fof(f4283,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0)
    | ~ spl15_63 ),
    inference(avatar_component_clause,[],[f4282])).

fof(f4282,plain,
    ( spl15_63
  <=> ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_63])])).

fof(f4284,plain,
    ( ~ spl15_61
    | ~ spl15_63
    | spl15_37 ),
    inference(avatar_split_clause,[],[f4244,f3758,f4282,f4276])).

fof(f4244,plain,
    ( ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK0)
    | ~ r2_hidden(sK14(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),sK0),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl15_37 ),
    inference(extensionality_resolution,[],[f74,f3759])).

fof(f4270,plain,
    ( spl15_37
    | spl15_57
    | spl15_59 ),
    inference(avatar_contradiction_clause,[],[f4269])).

fof(f4269,plain,
    ( $false
    | ~ spl15_37
    | ~ spl15_57
    | ~ spl15_59 ),
    inference(subsumption_resolution,[],[f4268,f3759])).

fof(f4268,plain,
    ( sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_57
    | ~ spl15_59 ),
    inference(subsumption_resolution,[],[f4267,f4256])).

fof(f4256,plain,
    ( ~ r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0)
    | ~ spl15_57 ),
    inference(avatar_component_clause,[],[f4255])).

fof(f4255,plain,
    ( spl15_57
  <=> ~ r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).

fof(f4263,plain,
    ( ~ spl15_57
    | ~ spl15_59
    | spl15_37 ),
    inference(avatar_split_clause,[],[f4243,f3758,f4261,f4255])).

fof(f4243,plain,
    ( ~ r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ r2_hidden(sK14(sK0,sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),sK0)
    | ~ spl15_37 ),
    inference(extensionality_resolution,[],[f74,f3759])).

fof(f4239,plain,
    ( spl15_11
    | ~ spl15_52 ),
    inference(avatar_contradiction_clause,[],[f4238])).

fof(f4238,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f4203,f111])).

fof(f4203,plain,
    ( ~ r2_hidden(sK2,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_52 ),
    inference(backward_demodulation,[],[f3810,f218])).

fof(f218,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11 ),
    inference(resolution,[],[f213,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f213,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl15_11
  <=> ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f4196,plain,
    ( spl15_11
    | ~ spl15_50 ),
    inference(avatar_contradiction_clause,[],[f4195])).

fof(f4195,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_50 ),
    inference(subsumption_resolution,[],[f4161,f109])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X2,X10,X4,X5,X6,X7,X8)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X10,X4,X5,X6,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X3 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4161,plain,
    ( ~ r2_hidden(sK3,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_50 ),
    inference(backward_demodulation,[],[f3804,f218])).

fof(f4154,plain,
    ( spl15_11
    | ~ spl15_48 ),
    inference(avatar_contradiction_clause,[],[f4153])).

fof(f4153,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_48 ),
    inference(subsumption_resolution,[],[f4120,f107])).

fof(f107,plain,(
    ! [X6,X2,X0,X10,X8,X7,X5,X3,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X2,X3,X10,X5,X6,X7,X8)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X6,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X10,X5,X6,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X4 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4120,plain,
    ( ~ r2_hidden(sK4,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_48 ),
    inference(backward_demodulation,[],[f3798,f218])).

fof(f4113,plain,
    ( spl15_11
    | ~ spl15_44 ),
    inference(avatar_contradiction_clause,[],[f4112])).

fof(f4112,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f4081,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X10,X8,X7,X5,X3,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X2,X3,X4,X5,X10,X7,X8)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X10,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X6 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4081,plain,
    ( ~ r2_hidden(sK6,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_44 ),
    inference(backward_demodulation,[],[f3786,f218])).

fof(f4075,plain,
    ( spl15_11
    | ~ spl15_40 ),
    inference(avatar_contradiction_clause,[],[f4074])).

fof(f4074,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_40 ),
    inference(subsumption_resolution,[],[f4044,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X10)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X10) != X9 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X8 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4044,plain,
    ( ~ r2_hidden(sK8,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_40 ),
    inference(backward_demodulation,[],[f3774,f218])).

fof(f4038,plain,
    ( spl15_11
    | ~ spl15_36 ),
    inference(avatar_contradiction_clause,[],[f4037])).

fof(f4037,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_36 ),
    inference(subsumption_resolution,[],[f3999,f115])).

fof(f115,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : r2_hidden(X10,k7_enumset1(X10,X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X10,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X0 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3999,plain,
    ( ~ r2_hidden(sK0,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_36 ),
    inference(backward_demodulation,[],[f3762,f218])).

fof(f3992,plain,
    ( spl15_11
    | ~ spl15_46 ),
    inference(avatar_contradiction_clause,[],[f3991])).

fof(f3991,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f3959,f105])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X3,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X2,X3,X4,X10,X6,X7,X8)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X10,X6,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X5 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3959,plain,
    ( ~ r2_hidden(sK5,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_46 ),
    inference(backward_demodulation,[],[f3792,f218])).

fof(f3953,plain,
    ( spl15_11
    | ~ spl15_38 ),
    inference(avatar_contradiction_clause,[],[f3952])).

fof(f3952,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f3922,f122])).

fof(f3922,plain,
    ( ~ r2_hidden(sK9,k1_tarski(sK9))
    | ~ spl15_11
    | ~ spl15_38 ),
    inference(backward_demodulation,[],[f3768,f217])).

fof(f217,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k1_tarski(sK9))
    | ~ spl15_11 ),
    inference(resolution,[],[f213,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3916,plain,
    ( spl15_11
    | ~ spl15_42 ),
    inference(avatar_contradiction_clause,[],[f3915])).

fof(f3915,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f3914,f101])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X10,X8,X5,X3,X1] : r2_hidden(X10,k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X10,X8)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X10,X8,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X10,X8) != X9 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X7 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3914,plain,
    ( ~ r2_hidden(sK7,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_42 ),
    inference(forward_demodulation,[],[f218,f3780])).

fof(f3912,plain,
    ( spl15_11
    | ~ spl15_42 ),
    inference(avatar_contradiction_clause,[],[f3911])).

fof(f3911,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f3910,f101])).

fof(f3910,plain,
    ( ~ r2_hidden(sK7,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_42 ),
    inference(forward_demodulation,[],[f609,f3780])).

fof(f609,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11 ),
    inference(resolution,[],[f213,f117])).

fof(f3909,plain,
    ( spl15_19
    | ~ spl15_42 ),
    inference(avatar_contradiction_clause,[],[f3908])).

fof(f3908,plain,
    ( $false
    | ~ spl15_19
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f3907,f101])).

fof(f3907,plain,
    ( ~ r2_hidden(sK7,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_19
    | ~ spl15_42 ),
    inference(forward_demodulation,[],[f597,f3780])).

fof(f597,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl15_19
  <=> ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f3873,plain,
    ( spl15_9
    | ~ spl15_54 ),
    inference(avatar_contradiction_clause,[],[f3872])).

fof(f3872,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_54 ),
    inference(subsumption_resolution,[],[f3871,f94])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] : r2_hidden(X11,k8_enumset1(X0,X11,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X11,X9] :
      ( r2_hidden(X11,X10)
      | k8_enumset1(X0,X11,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X1 != X11
      | r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3871,plain,
    ( ~ r2_hidden(sK1,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_9
    | ~ spl15_54 ),
    inference(forward_demodulation,[],[f207,f3816])).

fof(f3816,plain,
    ( sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_54 ),
    inference(avatar_component_clause,[],[f3815])).

fof(f3815,plain,
    ( spl15_54
  <=> sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f3868,plain,
    ( spl15_11
    | ~ spl15_54 ),
    inference(avatar_contradiction_clause,[],[f3867])).

fof(f3867,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_54 ),
    inference(subsumption_resolution,[],[f3866,f113])).

fof(f113,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3] : r2_hidden(X10,k7_enumset1(X0,X10,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X9] :
      ( r2_hidden(X10,X9)
      | k7_enumset1(X0,X10,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X1 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3866,plain,
    ( ~ r2_hidden(sK1,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_54 ),
    inference(forward_demodulation,[],[f218,f3816])).

fof(f3865,plain,
    ( spl15_11
    | ~ spl15_54 ),
    inference(avatar_contradiction_clause,[],[f3864])).

fof(f3864,plain,
    ( $false
    | ~ spl15_11
    | ~ spl15_54 ),
    inference(subsumption_resolution,[],[f3863,f113])).

fof(f3863,plain,
    ( ~ r2_hidden(sK1,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11
    | ~ spl15_54 ),
    inference(forward_demodulation,[],[f609,f3816])).

fof(f3852,plain,
    ( spl15_19
    | ~ spl15_54 ),
    inference(avatar_contradiction_clause,[],[f3851])).

fof(f3851,plain,
    ( $false
    | ~ spl15_19
    | ~ spl15_54 ),
    inference(subsumption_resolution,[],[f3821,f113])).

fof(f3821,plain,
    ( ~ r2_hidden(sK1,k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_19
    | ~ spl15_54 ),
    inference(backward_demodulation,[],[f3816,f597])).

fof(f3817,plain,
    ( spl15_36
    | spl15_38
    | spl15_40
    | spl15_42
    | spl15_44
    | spl15_46
    | spl15_48
    | spl15_50
    | spl15_52
    | spl15_54
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f603,f203,f3815,f3809,f3803,f3797,f3791,f3785,f3779,f3773,f3767,f3761])).

fof(f203,plain,
    ( spl15_8
  <=> r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f603,plain,
    ( sK1 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK2 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK3 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK4 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK5 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK6 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK7 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK8 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK9 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | sK0 = sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_8 ),
    inference(resolution,[],[f204,f97])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( ~ r2_hidden(X11,k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))
      | X1 = X11
      | X2 = X11
      | X3 = X11
      | X4 = X11
      | X5 = X11
      | X6 = X11
      | X7 = X11
      | X8 = X11
      | X9 = X11
      | X0 = X11 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( X0 = X11
      | X1 = X11
      | X2 = X11
      | X3 = X11
      | X4 = X11
      | X5 = X11
      | X6 = X11
      | X7 = X11
      | X8 = X11
      | X9 = X11
      | ~ r2_hidden(X11,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f204,plain,
    ( r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f3374,plain,
    ( spl15_34
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f660,f187,f3372])).

fof(f3372,plain,
    ( spl15_34
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).

fof(f187,plain,
    ( spl15_6
  <=> r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f660,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_6 ),
    inference(resolution,[],[f188,f281])).

fof(f188,plain,
    ( r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f187])).

fof(f3280,plain,
    ( spl15_32
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f659,f187,f3278])).

fof(f3278,plain,
    ( spl15_32
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f659,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))
    | ~ spl15_6 ),
    inference(resolution,[],[f188,f360])).

fof(f3186,plain,
    ( spl15_30
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f606,f203,f3184])).

fof(f3184,plain,
    ( spl15_30
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).

fof(f606,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_8 ),
    inference(resolution,[],[f204,f281])).

fof(f3092,plain,
    ( spl15_28
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f605,f203,f3090])).

fof(f3090,plain,
    ( spl15_28
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f605,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_tarski(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))))
    | ~ spl15_8 ),
    inference(resolution,[],[f204,f360])).

fof(f728,plain,
    ( ~ spl15_27
    | spl15_21 ),
    inference(avatar_split_clause,[],[f714,f611,f726])).

fof(f726,plain,
    ( spl15_27
  <=> ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_27])])).

fof(f611,plain,
    ( spl15_21
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).

fof(f714,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_21 ),
    inference(subsumption_resolution,[],[f712,f118])).

fof(f712,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))))
    | ~ spl15_21 ),
    inference(extensionality_resolution,[],[f74,f612])).

fof(f612,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))
    | ~ spl15_21 ),
    inference(avatar_component_clause,[],[f611])).

fof(f721,plain,
    ( ~ spl15_25
    | spl15_21 ),
    inference(avatar_split_clause,[],[f713,f611,f719])).

fof(f719,plain,
    ( spl15_25
  <=> ~ r2_hidden(sK14(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_25])])).

fof(f713,plain,
    ( ~ r2_hidden(sK14(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_21 ),
    inference(subsumption_resolution,[],[f711,f118])).

fof(f711,plain,
    ( ~ r2_hidden(sK14(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))))
    | ~ r2_hidden(sK14(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_21 ),
    inference(extensionality_resolution,[],[f74,f612])).

fof(f669,plain,
    ( ~ spl15_20
    | spl15_23 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | ~ spl15_20
    | ~ spl15_23 ),
    inference(subsumption_resolution,[],[f664,f652])).

fof(f652,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_23 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl15_23
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f664,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_20 ),
    inference(superposition,[],[f461,f615])).

fof(f615,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f614])).

fof(f614,plain,
    ( spl15_20
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f461,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k1_tarski(X3)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(X4,k1_tarski(X3))) ),
    inference(superposition,[],[f424,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',commutativity_k2_xboole_0)).

fof(f424,plain,(
    ! [X200,X201] : k2_xboole_0(k1_tarski(X200),X201) = k2_xboole_0(k1_tarski(X200),k2_xboole_0(k1_tarski(X200),X201)) ),
    inference(resolution,[],[f308,f122])).

fof(f308,plain,(
    ! [X182,X184,X183] :
      ( ~ r2_hidden(X182,X183)
      | k2_xboole_0(X183,X184) = k2_xboole_0(k1_tarski(X182),k2_xboole_0(X183,X184)) ) ),
    inference(resolution,[],[f281,f118])).

fof(f656,plain,
    ( spl15_22
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f588,f560,f654])).

fof(f654,plain,
    ( spl15_22
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f560,plain,
    ( spl15_14
  <=> r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f588,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_14 ),
    inference(resolution,[],[f561,f281])).

fof(f561,plain,
    ( r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f560])).

fof(f616,plain,
    ( spl15_20
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f587,f560,f614])).

fof(f587,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))))
    | ~ spl15_14 ),
    inference(resolution,[],[f561,f360])).

fof(f601,plain,
    ( spl15_16
    | spl15_18
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f222,f209,f599,f593])).

fof(f209,plain,
    ( spl15_10
  <=> r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f222,plain,
    ( r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k1_tarski(sK9))
    | ~ spl15_10 ),
    inference(resolution,[],[f210,f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f210,plain,
    ( r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f209])).

fof(f575,plain,
    ( spl15_7
    | ~ spl15_12 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl15_7
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f568,f78])).

fof(f568,plain,
    ( ~ r2_hidden(sK9,k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_7
    | ~ spl15_12 ),
    inference(backward_demodulation,[],[f563,f191])).

fof(f191,plain,
    ( ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl15_7
  <=> ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f563,plain,
    ( sK9 = sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ spl15_12 ),
    inference(resolution,[],[f555,f120])).

fof(f555,plain,
    ( r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k1_tarski(sK9))
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl15_12
  <=> r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k1_tarski(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f562,plain,
    ( spl15_12
    | spl15_14
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f201,f181,f560,f554])).

fof(f181,plain,
    ( spl15_4
  <=> r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f201,plain,
    ( r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k1_tarski(sK9))
    | ~ spl15_4 ),
    inference(resolution,[],[f182,f119])).

fof(f182,plain,
    ( r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f181])).

fof(f221,plain,
    ( spl15_3
    | spl15_9
    | spl15_11 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_9
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f219,f137])).

fof(f137,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl15_3
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f219,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_9
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f216,f207])).

fof(f216,plain,
    ( r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_11 ),
    inference(resolution,[],[f213,f73])).

fof(f214,plain,
    ( ~ spl15_9
    | ~ spl15_11
    | spl15_1 ),
    inference(avatar_split_clause,[],[f169,f127,f212,f206])).

fof(f127,plain,
    ( spl15_1
  <=> k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f169,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_1 ),
    inference(forward_demodulation,[],[f168,f75])).

fof(f168,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)))
    | ~ spl15_1 ),
    inference(forward_demodulation,[],[f158,f75])).

fof(f158,plain,
    ( ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ r2_hidden(sK14(k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)))
    | ~ spl15_1 ),
    inference(extensionality_resolution,[],[f74,f128])).

fof(f128,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f199,plain,
    ( spl15_3
    | spl15_5
    | spl15_7 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f197,f137])).

fof(f197,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f194,f191])).

fof(f194,plain,
    ( r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) = k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_5 ),
    inference(resolution,[],[f185,f73])).

fof(f185,plain,
    ( ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl15_5
  <=> ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f192,plain,
    ( ~ spl15_5
    | ~ spl15_7
    | spl15_1 ),
    inference(avatar_split_clause,[],[f167,f127,f190,f184])).

fof(f167,plain,
    ( ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ spl15_1 ),
    inference(forward_demodulation,[],[f166,f75])).

fof(f166,plain,
    ( ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)))
    | ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_1 ),
    inference(forward_demodulation,[],[f157,f75])).

fof(f157,plain,
    ( ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9))),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)))
    | ~ r2_hidden(sK14(k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9),k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9))),k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl15_1 ),
    inference(extensionality_resolution,[],[f74,f128])).

fof(f138,plain,
    ( ~ spl15_3
    | spl15_1 ),
    inference(avatar_split_clause,[],[f130,f127,f136])).

fof(f130,plain,
    ( k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k1_tarski(sK9),k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl15_1 ),
    inference(superposition,[],[f128,f75])).

fof(f129,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f20,f127])).

fof(f20,plain,(
    k8_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) != k2_xboole_0(k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK9)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t135_enumset1.p',t135_enumset1)).
%------------------------------------------------------------------------------
