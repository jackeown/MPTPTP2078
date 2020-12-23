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
% DateTime   : Thu Dec  3 12:31:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 833 expanded)
%              Number of leaves         :   50 ( 316 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 (1237 expanded)
%              Number of equality atoms :   54 ( 508 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4470,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f54,f59,f74,f119,f159,f431,f2857,f2894,f2899,f2904,f2909,f3241,f3246,f3251,f3256,f3285,f3290,f3295,f3300,f3305,f3387,f3392,f3397,f3402,f4323,f4328,f4333,f4338,f4343,f4348,f4353,f4358,f4363,f4432,f4437,f4442,f4447,f4465,f4469])).

fof(f4469,plain,
    ( spl3_3
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f4468])).

fof(f4468,plain,
    ( $false
    | spl3_3
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f4467,f69])).

fof(f69,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f67,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f67,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f53,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f4467,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f4466,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f4466,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f4460,f26])).

fof(f4460,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl3_38 ),
    inference(resolution,[],[f4436,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4436,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f4434])).

fof(f4434,plain,
    ( spl3_38
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f4465,plain,
    ( spl3_3
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f4464])).

fof(f4464,plain,
    ( $false
    | spl3_3
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f4463,f69])).

fof(f4463,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f4462,f22])).

fof(f4462,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f4458,f26])).

fof(f4458,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f4436,f29])).

fof(f4447,plain,
    ( spl3_40
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f4380,f4320,f4444])).

fof(f4444,plain,
    ( spl3_40
  <=> r1_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f4320,plain,
    ( spl3_28
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f4380,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_28 ),
    inference(superposition,[],[f43,f4322])).

fof(f4322,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f4320])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f4442,plain,
    ( spl3_39
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f4375,f4320,f4439])).

fof(f4439,plain,
    ( spl3_39
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f4375,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK0))
    | ~ spl3_28 ),
    inference(superposition,[],[f19,f4322])).

fof(f4437,plain,
    ( spl3_38
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f4367,f4320,f4434])).

fof(f4367,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_28 ),
    inference(superposition,[],[f221,f4322])).

fof(f221,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f189,f22])).

fof(f189,plain,(
    ! [X12,X13,X11] : r1_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f43,f26])).

fof(f4432,plain,
    ( spl3_37
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f4366,f4320,f4429])).

fof(f4429,plain,
    ( spl3_37
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f4366,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))
    | ~ spl3_28 ),
    inference(superposition,[],[f207,f4322])).

fof(f207,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f190,f22])).

fof(f190,plain,(
    ! [X14,X15,X16] : r1_xboole_0(k4_xboole_0(X14,k2_xboole_0(X15,X16)),X16) ),
    inference(superposition,[],[f19,f26])).

fof(f4363,plain,
    ( spl3_36
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3485,f3399,f4360])).

fof(f4360,plain,
    ( spl3_36
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f3399,plain,
    ( spl3_27
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f3485,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0),k4_xboole_0(sK1,sK2))
    | ~ spl3_27 ),
    inference(superposition,[],[f548,f3401])).

fof(f3401,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f3399])).

fof(f548,plain,(
    ! [X8,X9] : r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,X9),k1_xboole_0),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f469,f176])).

fof(f176,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f26,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f469,plain,(
    ! [X19,X20] : r1_xboole_0(k2_xboole_0(X20,k1_xboole_0),k4_xboole_0(X19,X20)) ),
    inference(superposition,[],[f43,f182])).

fof(f182,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f26,f18])).

fof(f4358,plain,
    ( spl3_35
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3484,f3399,f4355])).

fof(f4355,plain,
    ( spl3_35
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f3484,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0),k4_xboole_0(sK1,sK2))
    | ~ spl3_27 ),
    inference(superposition,[],[f547,f3401])).

fof(f547,plain,(
    ! [X6,X7] : r1_xboole_0(k2_xboole_0(k2_xboole_0(X7,k1_xboole_0),k1_xboole_0),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f469,f182])).

fof(f4353,plain,
    ( spl3_34
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3481,f3399,f4350])).

fof(f4350,plain,
    ( spl3_34
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f3481,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0))
    | ~ spl3_27 ),
    inference(superposition,[],[f523,f3401])).

fof(f523,plain,(
    ! [X8,X9] : r1_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(k2_xboole_0(k1_xboole_0,X9),k1_xboole_0)) ),
    inference(superposition,[],[f465,f176])).

fof(f465,plain,(
    ! [X10,X11] : r1_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X11,k1_xboole_0)) ),
    inference(superposition,[],[f19,f182])).

fof(f4348,plain,
    ( spl3_33
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3480,f3399,f4345])).

fof(f4345,plain,
    ( spl3_33
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f3480,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0))
    | ~ spl3_27 ),
    inference(superposition,[],[f522,f3401])).

fof(f522,plain,(
    ! [X6,X7] : r1_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(k2_xboole_0(X7,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f465,f182])).

fof(f4343,plain,
    ( spl3_32
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3479,f3399,f4340])).

fof(f4340,plain,
    ( spl3_32
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f3479,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0)))
    | ~ spl3_27 ),
    inference(superposition,[],[f472,f3401])).

fof(f472,plain,(
    ! [X26,X25] : r1_xboole_0(k4_xboole_0(X25,X26),k2_xboole_0(k1_xboole_0,k2_xboole_0(X26,k1_xboole_0))) ),
    inference(superposition,[],[f343,f182])).

fof(f343,plain,(
    ! [X19,X18] : r1_xboole_0(k4_xboole_0(X18,X19),k2_xboole_0(k1_xboole_0,X19)) ),
    inference(superposition,[],[f19,f176])).

fof(f4338,plain,
    ( spl3_31
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3478,f3399,f4335])).

fof(f4335,plain,
    ( spl3_31
  <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f3478,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(sK1,sK2))
    | ~ spl3_27 ),
    inference(superposition,[],[f471,f3401])).

fof(f471,plain,(
    ! [X24,X23] : r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X24,k1_xboole_0)),k4_xboole_0(X23,X24)) ),
    inference(superposition,[],[f342,f182])).

fof(f342,plain,(
    ! [X17,X16] : r1_xboole_0(k2_xboole_0(k1_xboole_0,X17),k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f43,f176])).

fof(f4333,plain,
    ( spl3_30
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3475,f3399,f4330])).

fof(f4330,plain,
    ( spl3_30
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f3475,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0)))
    | ~ spl3_27 ),
    inference(superposition,[],[f386,f3401])).

fof(f386,plain,(
    ! [X8,X7] : r1_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X8))) ),
    inference(superposition,[],[f343,f176])).

fof(f4328,plain,
    ( spl3_29
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3474,f3399,f4325])).

fof(f4325,plain,
    ( spl3_29
  <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f3474,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0)),k4_xboole_0(sK1,sK2))
    | ~ spl3_27 ),
    inference(superposition,[],[f359,f3401])).

fof(f359,plain,(
    ! [X8,X7] : r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X8)),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f342,f176])).

fof(f4323,plain,
    ( spl3_28
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f3463,f3399,f4320])).

fof(f3463,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_27 ),
    inference(superposition,[],[f3401,f26])).

fof(f3402,plain,
    ( spl3_27
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2969,f2854,f3399])).

fof(f2854,plain,
    ( spl3_10
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f2969,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f2829,f2856])).

fof(f2856,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f2854])).

fof(f2829,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f2768,f18])).

fof(f2768,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f76])).

fof(f76,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f43,f29])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f3397,plain,
    ( spl3_26
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2879,f2854,f3394])).

fof(f3394,plain,
    ( spl3_26
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f2879,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f548,f2856])).

fof(f3392,plain,
    ( spl3_25
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2878,f2854,f3389])).

fof(f3389,plain,
    ( spl3_25
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f2878,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f547,f2856])).

fof(f3387,plain,
    ( spl3_24
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2875,f2854,f3384])).

fof(f3384,plain,
    ( spl3_24
  <=> r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f2875,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0))
    | ~ spl3_10 ),
    inference(superposition,[],[f523,f2856])).

fof(f3305,plain,
    ( spl3_23
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2874,f2854,f3302])).

fof(f3302,plain,
    ( spl3_23
  <=> r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f2874,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0))
    | ~ spl3_10 ),
    inference(superposition,[],[f522,f2856])).

fof(f3300,plain,
    ( spl3_22
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2873,f2854,f3297])).

fof(f3297,plain,
    ( spl3_22
  <=> r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f2873,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)))
    | ~ spl3_10 ),
    inference(superposition,[],[f472,f2856])).

fof(f3295,plain,
    ( spl3_21
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2872,f2854,f3292])).

fof(f3292,plain,
    ( spl3_21
  <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f2872,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f471,f2856])).

fof(f3290,plain,
    ( spl3_20
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2869,f2854,f3287])).

fof(f3287,plain,
    ( spl3_20
  <=> r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2869,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_10 ),
    inference(superposition,[],[f386,f2856])).

fof(f3285,plain,
    ( spl3_19
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2868,f2854,f3282])).

fof(f3282,plain,
    ( spl3_19
  <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f2868,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f359,f2856])).

fof(f3256,plain,
    ( spl3_18
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3216,f2854,f3253])).

fof(f3253,plain,
    ( spl3_18
  <=> r1_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f3216,plain,
    ( r1_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(superposition,[],[f2985,f2856])).

fof(f2985,plain,(
    ! [X35,X34] : r1_xboole_0(k2_xboole_0(k4_xboole_0(X35,X34),k1_xboole_0),X34) ),
    inference(superposition,[],[f469,f2829])).

fof(f3251,plain,
    ( spl3_17
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3160,f2854,f3248])).

fof(f3248,plain,
    ( spl3_17
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f3160,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_10 ),
    inference(superposition,[],[f2984,f2856])).

fof(f2984,plain,(
    ! [X33,X32] : r1_xboole_0(X32,k2_xboole_0(k4_xboole_0(X33,X32),k1_xboole_0)) ),
    inference(superposition,[],[f465,f2829])).

fof(f3246,plain,
    ( spl3_16
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3103,f2854,f3243])).

fof(f3243,plain,
    ( spl3_16
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f3103,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK0))
    | ~ spl3_10 ),
    inference(superposition,[],[f2981,f2856])).

fof(f2981,plain,(
    ! [X26,X27] : r1_xboole_0(X26,k2_xboole_0(k1_xboole_0,k4_xboole_0(X27,X26))) ),
    inference(superposition,[],[f343,f2829])).

fof(f3241,plain,
    ( spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3050,f2854,f3238])).

fof(f3238,plain,
    ( spl3_15
  <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f3050,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(superposition,[],[f2980,f2856])).

fof(f2980,plain,(
    ! [X24,X25] : r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X25,X24)),X24) ),
    inference(superposition,[],[f342,f2829])).

fof(f2909,plain,
    ( spl3_14
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2871,f2854,f2906])).

fof(f2906,plain,
    ( spl3_14
  <=> r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f2871,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f469,f2856])).

fof(f2904,plain,
    ( spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2870,f2854,f2901])).

fof(f2901,plain,
    ( spl3_13
  <=> r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f2870,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))
    | ~ spl3_10 ),
    inference(superposition,[],[f465,f2856])).

fof(f2899,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2867,f2854,f2896])).

fof(f2896,plain,
    ( spl3_12
  <=> r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f2867,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_10 ),
    inference(superposition,[],[f343,f2856])).

fof(f2894,plain,
    ( spl3_11
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2866,f2854,f2891])).

fof(f2891,plain,
    ( spl3_11
  <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f2866,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_10 ),
    inference(superposition,[],[f342,f2856])).

fof(f2857,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f2836,f116,f2854])).

fof(f116,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f2836,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f2771,f18])).

fof(f2771,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f27,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f431,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f402,f428])).

fof(f428,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f402,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f328,f18])).

fof(f328,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3) ),
    inference(superposition,[],[f176,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f75,f18])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f19,f18])).

fof(f159,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f129,f116,f156,f152])).

fof(f152,plain,
    ( spl3_7
  <=> r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f156,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f129,plain,
    ( k1_xboole_0 != sK0
    | r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f123,f18])).

fof(f123,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)
    | r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(superposition,[],[f28,f118])).

fof(f119,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f80,f31,f116])).

fof(f31,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f33,f29])).

fof(f33,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f74,plain,
    ( ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f66,f36,f71])).

fof(f71,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f36,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f38,f28])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f59,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f42,f31,f56])).

fof(f56,plain,
    ( spl3_4
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f33,f23])).

fof(f54,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f41,f36,f51])).

fof(f41,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f38,f23])).

fof(f39,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (10727)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (10729)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (10721)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (10720)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (10735)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (10733)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (10723)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (10719)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (10724)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (10731)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (10726)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (10725)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (10722)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.51  % (10732)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (10736)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.52  % (10734)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.53  % (10730)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.55  % (10728)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.56  % (10727)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f4470,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f34,f39,f54,f59,f74,f119,f159,f431,f2857,f2894,f2899,f2904,f2909,f3241,f3246,f3251,f3256,f3285,f3290,f3295,f3300,f3305,f3387,f3392,f3397,f3402,f4323,f4328,f4333,f4338,f4343,f4348,f4353,f4358,f4363,f4432,f4437,f4442,f4447,f4465,f4469])).
% 0.20/0.56  fof(f4469,plain,(
% 0.20/0.56    spl3_3 | ~spl3_38),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f4468])).
% 0.20/0.56  fof(f4468,plain,(
% 0.20/0.56    $false | (spl3_3 | ~spl3_38)),
% 0.20/0.56    inference(subsumption_resolution,[],[f4467,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | spl3_3),
% 0.20/0.56    inference(forward_demodulation,[],[f67,f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | spl3_3),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f53,f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f25,f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    spl3_3 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.56  fof(f4467,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | ~spl3_38),
% 0.20/0.56    inference(forward_demodulation,[],[f4466,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.56  fof(f4466,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~spl3_38),
% 0.20/0.56    inference(forward_demodulation,[],[f4460,f26])).
% 0.20/0.56  fof(f4460,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) | ~spl3_38),
% 0.20/0.56    inference(resolution,[],[f4436,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f24,f20])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f4436,plain,(
% 0.20/0.56    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_38),
% 0.20/0.56    inference(avatar_component_clause,[],[f4434])).
% 0.20/0.56  fof(f4434,plain,(
% 0.20/0.56    spl3_38 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.56  fof(f4465,plain,(
% 0.20/0.56    spl3_3 | ~spl3_38),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f4464])).
% 0.20/0.56  fof(f4464,plain,(
% 0.20/0.56    $false | (spl3_3 | ~spl3_38)),
% 0.20/0.56    inference(subsumption_resolution,[],[f4463,f69])).
% 0.20/0.56  fof(f4463,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | ~spl3_38),
% 0.20/0.56    inference(forward_demodulation,[],[f4462,f22])).
% 0.20/0.56  fof(f4462,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~spl3_38),
% 0.20/0.56    inference(forward_demodulation,[],[f4458,f26])).
% 0.20/0.56  fof(f4458,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) | ~spl3_38),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f4436,f29])).
% 0.20/0.56  fof(f4447,plain,(
% 0.20/0.56    spl3_40 | ~spl3_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f4380,f4320,f4444])).
% 0.20/0.56  fof(f4444,plain,(
% 0.20/0.56    spl3_40 <=> r1_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.56  fof(f4320,plain,(
% 0.20/0.56    spl3_28 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.56  fof(f4380,plain,(
% 0.20/0.56    r1_xboole_0(k2_xboole_0(sK2,sK0),k4_xboole_0(sK1,sK2)) | ~spl3_28),
% 0.20/0.56    inference(superposition,[],[f43,f4322])).
% 0.20/0.56  fof(f4322,plain,(
% 0.20/0.56    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f4320])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f19,f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.56  fof(f4442,plain,(
% 0.20/0.56    spl3_39 | ~spl3_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f4375,f4320,f4439])).
% 0.20/0.56  fof(f4439,plain,(
% 0.20/0.56    spl3_39 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.56  fof(f4375,plain,(
% 0.20/0.56    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,sK0)) | ~spl3_28),
% 0.20/0.56    inference(superposition,[],[f19,f4322])).
% 0.20/0.56  fof(f4437,plain,(
% 0.20/0.56    spl3_38 | ~spl3_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f4367,f4320,f4434])).
% 0.20/0.56  fof(f4367,plain,(
% 0.20/0.56    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_28),
% 0.20/0.56    inference(superposition,[],[f221,f4322])).
% 0.20/0.56  fof(f221,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1)))) )),
% 0.20/0.56    inference(superposition,[],[f189,f22])).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    ( ! [X12,X13,X11] : (r1_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X12,X13)))) )),
% 0.20/0.56    inference(superposition,[],[f43,f26])).
% 0.20/0.56  fof(f4432,plain,(
% 0.20/0.56    spl3_37 | ~spl3_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f4366,f4320,f4429])).
% 0.20/0.56  fof(f4429,plain,(
% 0.20/0.56    spl3_37 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.56  fof(f4366,plain,(
% 0.20/0.56    r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) | ~spl3_28),
% 0.20/0.56    inference(superposition,[],[f207,f4322])).
% 0.20/0.56  fof(f207,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) )),
% 0.20/0.56    inference(superposition,[],[f190,f22])).
% 0.20/0.56  fof(f190,plain,(
% 0.20/0.56    ( ! [X14,X15,X16] : (r1_xboole_0(k4_xboole_0(X14,k2_xboole_0(X15,X16)),X16)) )),
% 0.20/0.56    inference(superposition,[],[f19,f26])).
% 0.20/0.56  fof(f4363,plain,(
% 0.20/0.56    spl3_36 | ~spl3_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f3485,f3399,f4360])).
% 0.20/0.56  fof(f4360,plain,(
% 0.20/0.56    spl3_36 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0),k4_xboole_0(sK1,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.56  fof(f3399,plain,(
% 0.20/0.56    spl3_27 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.56  fof(f3485,plain,(
% 0.20/0.56    r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0),k4_xboole_0(sK1,sK2)) | ~spl3_27),
% 0.20/0.56    inference(superposition,[],[f548,f3401])).
% 0.20/0.56  fof(f3401,plain,(
% 0.20/0.56    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_27),
% 0.20/0.56    inference(avatar_component_clause,[],[f3399])).
% 0.20/0.56  fof(f548,plain,(
% 0.20/0.56    ( ! [X8,X9] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,X9),k1_xboole_0),k4_xboole_0(X8,X9))) )),
% 0.20/0.56    inference(superposition,[],[f469,f176])).
% 0.20/0.56  fof(f176,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 0.20/0.56    inference(superposition,[],[f26,f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.56  fof(f469,plain,(
% 0.20/0.56    ( ! [X19,X20] : (r1_xboole_0(k2_xboole_0(X20,k1_xboole_0),k4_xboole_0(X19,X20))) )),
% 0.20/0.56    inference(superposition,[],[f43,f182])).
% 0.20/0.56  fof(f182,plain,(
% 0.20/0.56    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 0.20/0.56    inference(superposition,[],[f26,f18])).
% 0.20/0.56  fof(f4358,plain,(
% 0.20/0.56    spl3_35 | ~spl3_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f3484,f3399,f4355])).
% 0.20/0.56  fof(f4355,plain,(
% 0.20/0.56    spl3_35 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0),k4_xboole_0(sK1,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.56  fof(f3484,plain,(
% 0.20/0.56    r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0),k4_xboole_0(sK1,sK2)) | ~spl3_27),
% 0.20/0.56    inference(superposition,[],[f547,f3401])).
% 0.20/0.56  fof(f547,plain,(
% 0.20/0.56    ( ! [X6,X7] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X7,k1_xboole_0),k1_xboole_0),k4_xboole_0(X6,X7))) )),
% 0.20/0.56    inference(superposition,[],[f469,f182])).
% 0.20/0.56  fof(f4353,plain,(
% 0.20/0.56    spl3_34 | ~spl3_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f3481,f3399,f4350])).
% 0.20/0.56  fof(f4350,plain,(
% 0.20/0.56    spl3_34 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.56  fof(f3481,plain,(
% 0.20/0.56    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k1_xboole_0)) | ~spl3_27),
% 0.20/0.56    inference(superposition,[],[f523,f3401])).
% 0.20/0.56  fof(f523,plain,(
% 0.20/0.56    ( ! [X8,X9] : (r1_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(k2_xboole_0(k1_xboole_0,X9),k1_xboole_0))) )),
% 0.20/0.56    inference(superposition,[],[f465,f176])).
% 0.20/0.56  fof(f465,plain,(
% 0.20/0.56    ( ! [X10,X11] : (r1_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X11,k1_xboole_0))) )),
% 0.20/0.56    inference(superposition,[],[f19,f182])).
% 0.20/0.56  fof(f4348,plain,(
% 0.20/0.56    spl3_33 | ~spl3_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f3480,f3399,f4345])).
% 0.20/0.56  fof(f4345,plain,(
% 0.20/0.56    spl3_33 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.56  fof(f3480,plain,(
% 0.20/0.56    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0)) | ~spl3_27),
% 0.20/0.56    inference(superposition,[],[f522,f3401])).
% 0.20/0.56  fof(f522,plain,(
% 0.20/0.56    ( ! [X6,X7] : (r1_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(k2_xboole_0(X7,k1_xboole_0),k1_xboole_0))) )),
% 0.20/0.56    inference(superposition,[],[f465,f182])).
% 0.20/0.56  fof(f4343,plain,(
% 0.20/0.56    spl3_32 | ~spl3_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f3479,f3399,f4340])).
% 0.20/0.57  fof(f4340,plain,(
% 0.20/0.57    spl3_32 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.57  fof(f3479,plain,(
% 0.20/0.57    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0))) | ~spl3_27),
% 0.20/0.57    inference(superposition,[],[f472,f3401])).
% 0.20/0.57  fof(f472,plain,(
% 0.20/0.57    ( ! [X26,X25] : (r1_xboole_0(k4_xboole_0(X25,X26),k2_xboole_0(k1_xboole_0,k2_xboole_0(X26,k1_xboole_0)))) )),
% 0.20/0.57    inference(superposition,[],[f343,f182])).
% 0.20/0.57  fof(f343,plain,(
% 0.20/0.57    ( ! [X19,X18] : (r1_xboole_0(k4_xboole_0(X18,X19),k2_xboole_0(k1_xboole_0,X19))) )),
% 0.20/0.57    inference(superposition,[],[f19,f176])).
% 0.20/0.57  fof(f4338,plain,(
% 0.20/0.57    spl3_31 | ~spl3_27),
% 0.20/0.57    inference(avatar_split_clause,[],[f3478,f3399,f4335])).
% 0.20/0.57  fof(f4335,plain,(
% 0.20/0.57    spl3_31 <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.57  fof(f3478,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(sK1,sK2)) | ~spl3_27),
% 0.20/0.57    inference(superposition,[],[f471,f3401])).
% 0.20/0.57  fof(f471,plain,(
% 0.20/0.57    ( ! [X24,X23] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X24,k1_xboole_0)),k4_xboole_0(X23,X24))) )),
% 0.20/0.57    inference(superposition,[],[f342,f182])).
% 0.20/0.57  fof(f342,plain,(
% 0.20/0.57    ( ! [X17,X16] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,X17),k4_xboole_0(X16,X17))) )),
% 0.20/0.57    inference(superposition,[],[f43,f176])).
% 0.20/0.57  fof(f4333,plain,(
% 0.20/0.57    spl3_30 | ~spl3_27),
% 0.20/0.57    inference(avatar_split_clause,[],[f3475,f3399,f4330])).
% 0.20/0.57  fof(f4330,plain,(
% 0.20/0.57    spl3_30 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.57  fof(f3475,plain,(
% 0.20/0.57    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0))) | ~spl3_27),
% 0.20/0.57    inference(superposition,[],[f386,f3401])).
% 0.20/0.57  fof(f386,plain,(
% 0.20/0.57    ( ! [X8,X7] : (r1_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X8)))) )),
% 0.20/0.57    inference(superposition,[],[f343,f176])).
% 0.20/0.57  fof(f4328,plain,(
% 0.20/0.57    spl3_29 | ~spl3_27),
% 0.20/0.57    inference(avatar_split_clause,[],[f3474,f3399,f4325])).
% 0.20/0.57  fof(f4325,plain,(
% 0.20/0.57    spl3_29 <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0)),k4_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.57  fof(f3474,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK0)),k4_xboole_0(sK1,sK2)) | ~spl3_27),
% 0.20/0.57    inference(superposition,[],[f359,f3401])).
% 0.20/0.57  fof(f359,plain,(
% 0.20/0.57    ( ! [X8,X7] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X8)),k4_xboole_0(X7,X8))) )),
% 0.20/0.57    inference(superposition,[],[f342,f176])).
% 0.20/0.57  fof(f4323,plain,(
% 0.20/0.57    spl3_28 | ~spl3_27),
% 0.20/0.57    inference(avatar_split_clause,[],[f3463,f3399,f4320])).
% 0.20/0.57  fof(f3463,plain,(
% 0.20/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_27),
% 0.20/0.57    inference(superposition,[],[f3401,f26])).
% 0.20/0.57  fof(f3402,plain,(
% 0.20/0.57    spl3_27 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2969,f2854,f3399])).
% 0.20/0.57  fof(f2854,plain,(
% 0.20/0.57    spl3_10 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.57  fof(f2969,plain,(
% 0.20/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f2829,f2856])).
% 0.20/0.57  fof(f2856,plain,(
% 0.20/0.57    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f2854])).
% 0.20/0.57  fof(f2829,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.20/0.57    inference(forward_demodulation,[],[f2768,f18])).
% 0.20/0.57  fof(f2768,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(superposition,[],[f27,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f43,f29])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f21,f20])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.57  fof(f3397,plain,(
% 0.20/0.57    spl3_26 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2879,f2854,f3394])).
% 0.20/0.57  fof(f3394,plain,(
% 0.20/0.57    spl3_26 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.57  fof(f2879,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0),sK0) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f548,f2856])).
% 0.20/0.57  fof(f3392,plain,(
% 0.20/0.57    spl3_25 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2878,f2854,f3389])).
% 0.20/0.57  fof(f3389,plain,(
% 0.20/0.57    spl3_25 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.57  fof(f2878,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0),sK0) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f547,f2856])).
% 0.20/0.57  fof(f3387,plain,(
% 0.20/0.57    spl3_24 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2875,f2854,f3384])).
% 0.20/0.57  fof(f3384,plain,(
% 0.20/0.57    spl3_24 <=> r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.57  fof(f2875,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0)) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f523,f2856])).
% 0.20/0.57  fof(f3305,plain,(
% 0.20/0.57    spl3_23 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2874,f2854,f3302])).
% 0.20/0.57  fof(f3302,plain,(
% 0.20/0.57    spl3_23 <=> r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.57  fof(f2874,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0)) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f522,f2856])).
% 0.20/0.57  fof(f3300,plain,(
% 0.20/0.57    spl3_22 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2873,f2854,f3297])).
% 0.20/0.57  fof(f3297,plain,(
% 0.20/0.57    spl3_22 <=> r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.57  fof(f2873,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f472,f2856])).
% 0.20/0.57  fof(f3295,plain,(
% 0.20/0.57    spl3_21 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2872,f2854,f3292])).
% 0.20/0.57  fof(f3292,plain,(
% 0.20/0.57    spl3_21 <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.57  fof(f2872,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),sK0) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f471,f2856])).
% 0.20/0.57  fof(f3290,plain,(
% 0.20/0.57    spl3_20 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2869,f2854,f3287])).
% 0.20/0.57  fof(f3287,plain,(
% 0.20/0.57    spl3_20 <=> r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.57  fof(f2869,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f386,f2856])).
% 0.20/0.57  fof(f3285,plain,(
% 0.20/0.57    spl3_19 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f2868,f2854,f3282])).
% 0.20/0.57  fof(f3282,plain,(
% 0.20/0.57    spl3_19 <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.57  fof(f2868,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),sK0) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f359,f2856])).
% 0.20/0.57  fof(f3256,plain,(
% 0.20/0.57    spl3_18 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f3216,f2854,f3253])).
% 0.20/0.57  fof(f3253,plain,(
% 0.20/0.57    spl3_18 <=> r1_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.57  fof(f3216,plain,(
% 0.20/0.57    r1_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK1,sK2)) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f2985,f2856])).
% 0.20/0.57  fof(f2985,plain,(
% 0.20/0.57    ( ! [X35,X34] : (r1_xboole_0(k2_xboole_0(k4_xboole_0(X35,X34),k1_xboole_0),X34)) )),
% 0.20/0.57    inference(superposition,[],[f469,f2829])).
% 0.20/0.57  fof(f3251,plain,(
% 0.20/0.57    spl3_17 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f3160,f2854,f3248])).
% 0.20/0.57  fof(f3248,plain,(
% 0.20/0.57    spl3_17 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.57  fof(f3160,plain,(
% 0.20/0.57    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,k1_xboole_0)) | ~spl3_10),
% 0.20/0.57    inference(superposition,[],[f2984,f2856])).
% 1.75/0.58  fof(f2984,plain,(
% 1.75/0.58    ( ! [X33,X32] : (r1_xboole_0(X32,k2_xboole_0(k4_xboole_0(X33,X32),k1_xboole_0))) )),
% 1.75/0.58    inference(superposition,[],[f465,f2829])).
% 1.75/0.58  fof(f3246,plain,(
% 1.75/0.58    spl3_16 | ~spl3_10),
% 1.75/0.58    inference(avatar_split_clause,[],[f3103,f2854,f3243])).
% 1.75/0.58  fof(f3243,plain,(
% 1.75/0.58    spl3_16 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK0))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.75/0.58  fof(f3103,plain,(
% 1.75/0.58    r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK0)) | ~spl3_10),
% 1.75/0.58    inference(superposition,[],[f2981,f2856])).
% 1.75/0.58  fof(f2981,plain,(
% 1.75/0.58    ( ! [X26,X27] : (r1_xboole_0(X26,k2_xboole_0(k1_xboole_0,k4_xboole_0(X27,X26)))) )),
% 1.75/0.58    inference(superposition,[],[f343,f2829])).
% 1.75/0.58  fof(f3241,plain,(
% 1.75/0.58    spl3_15 | ~spl3_10),
% 1.75/0.58    inference(avatar_split_clause,[],[f3050,f2854,f3238])).
% 1.75/0.58  fof(f3238,plain,(
% 1.75/0.58    spl3_15 <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.75/0.58  fof(f3050,plain,(
% 1.75/0.58    r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK1,sK2)) | ~spl3_10),
% 1.75/0.58    inference(superposition,[],[f2980,f2856])).
% 1.75/0.58  fof(f2980,plain,(
% 1.75/0.58    ( ! [X24,X25] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X25,X24)),X24)) )),
% 1.75/0.58    inference(superposition,[],[f342,f2829])).
% 1.75/0.58  fof(f2909,plain,(
% 1.75/0.58    spl3_14 | ~spl3_10),
% 1.75/0.58    inference(avatar_split_clause,[],[f2871,f2854,f2906])).
% 1.75/0.58  fof(f2906,plain,(
% 1.75/0.58    spl3_14 <=> r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK0)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.75/0.58  fof(f2871,plain,(
% 1.75/0.58    r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK0) | ~spl3_10),
% 1.75/0.58    inference(superposition,[],[f469,f2856])).
% 1.75/0.58  fof(f2904,plain,(
% 1.75/0.58    spl3_13 | ~spl3_10),
% 1.75/0.58    inference(avatar_split_clause,[],[f2870,f2854,f2901])).
% 1.75/0.58  fof(f2901,plain,(
% 1.75/0.58    spl3_13 <=> r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.75/0.58  fof(f2870,plain,(
% 1.75/0.58    r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) | ~spl3_10),
% 1.75/0.58    inference(superposition,[],[f465,f2856])).
% 1.75/0.58  fof(f2899,plain,(
% 1.75/0.58    spl3_12 | ~spl3_10),
% 1.75/0.58    inference(avatar_split_clause,[],[f2867,f2854,f2896])).
% 1.75/0.58  fof(f2896,plain,(
% 1.75/0.58    spl3_12 <=> r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.75/0.58  fof(f2867,plain,(
% 1.75/0.58    r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) | ~spl3_10),
% 1.75/0.58    inference(superposition,[],[f343,f2856])).
% 1.75/0.58  fof(f2894,plain,(
% 1.75/0.58    spl3_11 | ~spl3_10),
% 1.75/0.58    inference(avatar_split_clause,[],[f2866,f2854,f2891])).
% 1.75/0.58  fof(f2891,plain,(
% 1.75/0.58    spl3_11 <=> r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.75/0.58  fof(f2866,plain,(
% 1.75/0.58    r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_10),
% 1.75/0.58    inference(superposition,[],[f342,f2856])).
% 1.75/0.58  fof(f2857,plain,(
% 1.75/0.58    spl3_10 | ~spl3_6),
% 1.75/0.58    inference(avatar_split_clause,[],[f2836,f116,f2854])).
% 1.75/0.58  fof(f116,plain,(
% 1.75/0.58    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.75/0.58  fof(f2836,plain,(
% 1.75/0.58    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_6),
% 1.75/0.58    inference(forward_demodulation,[],[f2771,f18])).
% 1.75/0.58  fof(f2771,plain,(
% 1.75/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_6),
% 1.75/0.58    inference(superposition,[],[f27,f118])).
% 1.75/0.58  fof(f118,plain,(
% 1.75/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_6),
% 1.75/0.58    inference(avatar_component_clause,[],[f116])).
% 1.75/0.58  fof(f431,plain,(
% 1.75/0.58    spl3_9),
% 1.75/0.58    inference(avatar_split_clause,[],[f402,f428])).
% 1.75/0.58  fof(f428,plain,(
% 1.75/0.58    spl3_9 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.75/0.58  fof(f402,plain,(
% 1.75/0.58    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.75/0.58    inference(superposition,[],[f328,f18])).
% 1.75/0.58  fof(f328,plain,(
% 1.75/0.58    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3)) )),
% 1.75/0.58    inference(superposition,[],[f176,f90])).
% 1.75/0.58  fof(f90,plain,(
% 1.75/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.75/0.58    inference(forward_demodulation,[],[f75,f18])).
% 1.75/0.58  fof(f75,plain,(
% 1.75/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f40,f29])).
% 1.75/0.58  fof(f40,plain,(
% 1.75/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.75/0.58    inference(superposition,[],[f19,f18])).
% 1.75/0.58  fof(f159,plain,(
% 1.75/0.58    spl3_7 | ~spl3_8 | ~spl3_6),
% 1.75/0.58    inference(avatar_split_clause,[],[f129,f116,f156,f152])).
% 1.75/0.58  fof(f152,plain,(
% 1.75/0.58    spl3_7 <=> r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.75/0.58  fof(f156,plain,(
% 1.75/0.58    spl3_8 <=> k1_xboole_0 = sK0),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.75/0.58  fof(f129,plain,(
% 1.75/0.58    k1_xboole_0 != sK0 | r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_6),
% 1.75/0.58    inference(forward_demodulation,[],[f123,f18])).
% 1.75/0.58  fof(f123,plain,(
% 1.75/0.58    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) | r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_6),
% 1.75/0.58    inference(superposition,[],[f28,f118])).
% 1.75/0.58  fof(f119,plain,(
% 1.75/0.58    spl3_6 | ~spl3_1),
% 1.75/0.58    inference(avatar_split_clause,[],[f80,f31,f116])).
% 1.75/0.58  fof(f31,plain,(
% 1.75/0.58    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.75/0.58  fof(f80,plain,(
% 1.75/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f33,f29])).
% 1.75/0.58  fof(f33,plain,(
% 1.75/0.58    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.75/0.58    inference(avatar_component_clause,[],[f31])).
% 1.75/0.58  fof(f74,plain,(
% 1.75/0.58    ~spl3_5 | spl3_2),
% 1.75/0.58    inference(avatar_split_clause,[],[f66,f36,f71])).
% 1.75/0.58  fof(f71,plain,(
% 1.75/0.58    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.75/0.58  fof(f36,plain,(
% 1.75/0.58    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.75/0.58  fof(f66,plain,(
% 1.75/0.58    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | spl3_2),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f38,f28])).
% 1.75/0.58  fof(f38,plain,(
% 1.75/0.58    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 1.75/0.58    inference(avatar_component_clause,[],[f36])).
% 1.75/0.58  fof(f59,plain,(
% 1.75/0.58    spl3_4 | ~spl3_1),
% 1.75/0.58    inference(avatar_split_clause,[],[f42,f31,f56])).
% 1.75/0.58  fof(f56,plain,(
% 1.75/0.58    spl3_4 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.75/0.58  fof(f42,plain,(
% 1.75/0.58    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_1),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f33,f23])).
% 1.75/0.58  fof(f54,plain,(
% 1.75/0.58    ~spl3_3 | spl3_2),
% 1.75/0.58    inference(avatar_split_clause,[],[f41,f36,f51])).
% 1.75/0.58  fof(f41,plain,(
% 1.75/0.58    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f38,f23])).
% 1.75/0.58  fof(f39,plain,(
% 1.75/0.58    ~spl3_2),
% 1.75/0.58    inference(avatar_split_clause,[],[f17,f36])).
% 1.75/0.58  fof(f17,plain,(
% 1.75/0.58    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.75/0.58    inference(cnf_transformation,[],[f14])).
% 1.75/0.58  fof(f14,plain,(
% 1.75/0.58    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.75/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 1.75/0.58  fof(f13,plain,(
% 1.75/0.58    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f11,plain,(
% 1.75/0.58    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f10])).
% 1.75/0.58  fof(f10,negated_conjecture,(
% 1.75/0.58    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.75/0.58    inference(negated_conjecture,[],[f9])).
% 1.75/0.58  fof(f9,conjecture,(
% 1.75/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.75/0.58  fof(f34,plain,(
% 1.75/0.58    spl3_1),
% 1.75/0.58    inference(avatar_split_clause,[],[f16,f31])).
% 1.75/0.58  fof(f16,plain,(
% 1.75/0.58    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.75/0.58    inference(cnf_transformation,[],[f14])).
% 1.75/0.58  % SZS output end Proof for theBenchmark
% 1.75/0.58  % (10727)------------------------------
% 1.75/0.58  % (10727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.58  % (10727)Termination reason: Refutation
% 1.75/0.58  
% 1.75/0.58  % (10727)Memory used [KB]: 8059
% 1.75/0.58  % (10727)Time elapsed: 0.143 s
% 1.75/0.58  % (10727)------------------------------
% 1.75/0.58  % (10727)------------------------------
% 1.75/0.58  % (10715)Success in time 0.222 s
%------------------------------------------------------------------------------
