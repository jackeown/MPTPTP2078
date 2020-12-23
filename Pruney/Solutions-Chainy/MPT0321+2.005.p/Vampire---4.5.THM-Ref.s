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
% DateTime   : Thu Dec  3 12:42:29 EST 2020

% Result     : Theorem 7.52s
% Output     : Refutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 452 expanded)
%              Number of leaves         :   49 ( 190 expanded)
%              Depth                    :    9
%              Number of atoms          :  491 (1072 expanded)
%              Number of equality atoms :  159 ( 470 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f59,f64,f274,f314,f347,f469,f481,f6210,f6357,f7047,f7175,f7415,f7610,f7666,f7729,f7874,f8246,f8254,f12136,f12260,f12367,f12370,f12371,f12373,f12665,f12824,f12831,f13309,f13324,f13414,f13593,f13744,f13820,f13885])).

fof(f13885,plain,
    ( spl4_1
    | ~ spl4_119
    | ~ spl4_143 ),
    inference(avatar_contradiction_clause,[],[f13884])).

fof(f13884,plain,
    ( $false
    | spl4_1
    | ~ spl4_119
    | ~ spl4_143 ),
    inference(subsumption_resolution,[],[f13883,f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f13883,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_119
    | ~ spl4_143 ),
    inference(subsumption_resolution,[],[f13827,f12664])).

fof(f12664,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_119 ),
    inference(avatar_component_clause,[],[f12662])).

fof(f12662,plain,
    ( spl4_119
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f13827,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_143 ),
    inference(superposition,[],[f72,f13759])).

fof(f13759,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_143 ),
    inference(avatar_component_clause,[],[f13757])).

fof(f13757,plain,
    ( spl4_143
  <=> sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f13820,plain,
    ( spl4_143
    | ~ spl4_141 ),
    inference(avatar_split_clause,[],[f13748,f13741,f13757])).

fof(f13741,plain,
    ( spl4_141
  <=> r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f13748,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_141 ),
    inference(subsumption_resolution,[],[f13747,f65])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f13747,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK0))
    | sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_141 ),
    inference(resolution,[],[f13743,f32])).

fof(f13743,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0)
    | ~ spl4_141 ),
    inference(avatar_component_clause,[],[f13741])).

fof(f13744,plain,
    ( spl4_141
    | ~ spl4_78
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f13732,f13590,f8244,f13741])).

fof(f8244,plain,
    ( spl4_78
  <=> ! [X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | r1_tarski(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f13590,plain,
    ( spl4_140
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f13732,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0)
    | ~ spl4_78
    | ~ spl4_140 ),
    inference(subsumption_resolution,[],[f13679,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13679,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0)
    | ~ spl4_78
    | ~ spl4_140 ),
    inference(superposition,[],[f8245,f13592])).

fof(f13592,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1)
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f13590])).

fof(f8245,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | r1_tarski(X5,sK0) )
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f8244])).

fof(f13593,plain,
    ( spl4_140
    | ~ spl4_129
    | ~ spl4_137 ),
    inference(avatar_split_clause,[],[f13498,f13411,f12808,f13590])).

fof(f12808,plain,
    ( spl4_129
  <=> ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).

fof(f13411,plain,
    ( spl4_137
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).

fof(f13498,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1)
    | ~ spl4_129
    | ~ spl4_137 ),
    inference(forward_demodulation,[],[f13000,f13413])).

fof(f13413,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_137 ),
    inference(avatar_component_clause,[],[f13411])).

fof(f13000,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1)
    | ~ spl4_129 ),
    inference(forward_demodulation,[],[f12929,f1762])).

fof(f1762,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_zfmisc_1(X7,k2_xboole_0(X9,X8)) ),
    inference(superposition,[],[f121,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f121,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X5,X6)) = k2_zfmisc_1(X5,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f35,f27])).

fof(f12929,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_xboole_0(sK1,k1_xboole_0)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1)
    | ~ spl4_129 ),
    inference(superposition,[],[f35,f12809])).

fof(f12809,plain,
    ( ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_129 ),
    inference(avatar_component_clause,[],[f12808])).

fof(f13414,plain,
    ( spl4_137
    | ~ spl4_136 ),
    inference(avatar_split_clause,[],[f13339,f13321,f13411])).

fof(f13321,plain,
    ( spl4_136
  <=> sK1 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f13339,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_136 ),
    inference(superposition,[],[f94,f13323])).

fof(f13323,plain,
    ( sK1 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_136 ),
    inference(avatar_component_clause,[],[f13321])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f76,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f13324,plain,
    ( spl4_136
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f13316,f13306,f13321])).

fof(f13306,plain,
    ( spl4_134
  <=> r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f13316,plain,
    ( sK1 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f13315,f166])).

fof(f166,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f116,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f116,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f65,f94])).

fof(f13315,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1)
    | sK1 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_134 ),
    inference(resolution,[],[f13308,f32])).

fof(f13308,plain,
    ( r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f13306])).

fof(f13309,plain,
    ( spl4_134
    | ~ spl4_80
    | ~ spl4_132 ),
    inference(avatar_split_clause,[],[f13283,f12828,f8252,f13306])).

fof(f8252,plain,
    ( spl4_80
  <=> ! [X6] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6))
        | r1_tarski(sK1,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f12828,plain,
    ( spl4_132
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f13283,plain,
    ( r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_80
    | ~ spl4_132 ),
    inference(subsumption_resolution,[],[f13227,f39])).

fof(f13227,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_80
    | ~ spl4_132 ),
    inference(superposition,[],[f8253,f12830])).

fof(f12830,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_132 ),
    inference(avatar_component_clause,[],[f12828])).

fof(f8253,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6))
        | r1_tarski(sK1,X6) )
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f8252])).

fof(f12831,plain,
    ( spl4_132
    | ~ spl4_12
    | ~ spl4_20
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f12778,f6975,f478,f341,f12828])).

fof(f341,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f478,plain,
    ( spl4_20
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f6975,plain,
    ( spl4_61
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f12778,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_12
    | ~ spl4_20
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f12777,f28])).

fof(f12777,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_20
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f12408,f343])).

fof(f343,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f341])).

fof(f12408,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl4_20
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f6977,f480])).

fof(f480,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f478])).

fof(f6977,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f6975])).

fof(f12824,plain,
    ( spl4_129
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f12793,f478,f341,f12808])).

fof(f12793,plain,
    ( ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f12422,f343])).

fof(f12422,plain,
    ( ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,sK3))
    | ~ spl4_20 ),
    inference(superposition,[],[f34,f480])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12665,plain,
    ( spl4_119
    | spl4_2
    | ~ spl4_18
    | ~ spl4_116 ),
    inference(avatar_split_clause,[],[f12658,f12257,f463,f47,f12662])).

fof(f47,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f463,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f12257,plain,
    ( spl4_116
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f12658,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_18
    | ~ spl4_116 ),
    inference(forward_demodulation,[],[f12375,f465])).

fof(f465,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f463])).

fof(f12375,plain,
    ( r1_tarski(sK0,sK2)
    | spl4_2
    | ~ spl4_116 ),
    inference(subsumption_resolution,[],[f12362,f49])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f12362,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_116 ),
    inference(resolution,[],[f12259,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f12259,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f12257])).

fof(f12373,plain,
    ( k1_xboole_0 != sK2
    | sK0 != sK2
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f12371,plain,
    ( k1_xboole_0 != sK3
    | sK1 != sK3
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f12370,plain,
    ( spl4_2
    | spl4_68
    | ~ spl4_116 ),
    inference(avatar_contradiction_clause,[],[f12369])).

fof(f12369,plain,
    ( $false
    | spl4_2
    | spl4_68
    | ~ spl4_116 ),
    inference(subsumption_resolution,[],[f12368,f49])).

fof(f12368,plain,
    ( k1_xboole_0 = sK1
    | spl4_68
    | ~ spl4_116 ),
    inference(subsumption_resolution,[],[f12362,f7728])).

fof(f7728,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_68 ),
    inference(avatar_component_clause,[],[f7726])).

fof(f7726,plain,
    ( spl4_68
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f12367,plain,
    ( ~ spl4_19
    | spl4_67
    | ~ spl4_116 ),
    inference(avatar_contradiction_clause,[],[f12366])).

fof(f12366,plain,
    ( $false
    | ~ spl4_19
    | spl4_67
    | ~ spl4_116 ),
    inference(subsumption_resolution,[],[f12361,f7665])).

fof(f7665,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl4_67 ),
    inference(avatar_component_clause,[],[f7663])).

fof(f7663,plain,
    ( spl4_67
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f12361,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl4_19
    | ~ spl4_116 ),
    inference(resolution,[],[f12259,f468])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
        | r1_tarski(sK3,X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
        | r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f12260,plain,
    ( spl4_116
    | ~ spl4_115 ),
    inference(avatar_split_clause,[],[f12160,f12068,f12257])).

fof(f12068,plain,
    ( spl4_115
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f12160,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_115 ),
    inference(superposition,[],[f306,f12070])).

fof(f12070,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f12068])).

fof(f306,plain,(
    ! [X10,X11,X9] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X10,X9),X11),k2_zfmisc_1(X9,X11)) ),
    inference(superposition,[],[f105,f110])).

fof(f110,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f94,f28])).

fof(f105,plain,(
    ! [X6,X8,X7] : r1_tarski(k2_zfmisc_1(X8,X7),k2_zfmisc_1(k2_xboole_0(X6,X8),X7)) ),
    inference(superposition,[],[f65,f34])).

fof(f12136,plain,
    ( spl4_115
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f11971,f5484,f12068])).

fof(f5484,plain,
    ( spl4_52
  <=> ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f11971,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl4_52 ),
    inference(superposition,[],[f154,f5485])).

fof(f5485,plain,
    ( ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3)))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f5484])).

fof(f154,plain,(
    ! [X14,X12,X13,X11] : k3_xboole_0(k2_zfmisc_1(X13,X11),k2_zfmisc_1(X14,k2_xboole_0(X11,X12))) = k2_zfmisc_1(k3_xboole_0(X13,X14),X11) ),
    inference(superposition,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f8254,plain,
    ( spl4_80
    | spl4_1
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f8201,f588,f42,f8252])).

fof(f588,plain,
    ( spl4_22
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f8201,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6))
        | r1_tarski(sK1,X6) )
    | spl4_1
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f8161,f44])).

fof(f8161,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6))
        | r1_tarski(sK1,X6)
        | k1_xboole_0 = sK0 )
    | ~ spl4_22 ),
    inference(superposition,[],[f37,f589])).

fof(f589,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f588])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8246,plain,
    ( spl4_78
    | spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f8200,f588,f47,f8244])).

fof(f8200,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | r1_tarski(X5,sK0) )
    | spl4_2
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f8160,f49])).

fof(f8160,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | r1_tarski(X5,sK0)
        | k1_xboole_0 = sK1 )
    | ~ spl4_22 ),
    inference(superposition,[],[f36,f589])).

fof(f7874,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f7729,plain,
    ( spl4_3
    | ~ spl4_68
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f7659,f7412,f7726,f52])).

fof(f52,plain,
    ( spl4_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f7412,plain,
    ( spl4_63
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f7659,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_63 ),
    inference(resolution,[],[f7414,f32])).

fof(f7414,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f7412])).

fof(f7666,plain,
    ( ~ spl4_67
    | spl4_4
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f7661,f7607,f56,f7663])).

fof(f56,plain,
    ( spl4_4
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f7607,plain,
    ( spl4_66
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f7661,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl4_4
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f7660,f58])).

fof(f58,plain,
    ( sK1 != sK3
    | spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f7660,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3
    | ~ spl4_66 ),
    inference(resolution,[],[f7609,f32])).

fof(f7609,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f7607])).

fof(f7610,plain,
    ( spl4_66
    | spl4_1
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f7282,f7172,f42,f7607])).

fof(f7172,plain,
    ( spl4_62
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f7282,plain,
    ( r1_tarski(sK1,sK3)
    | spl4_1
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f7280,f44])).

fof(f7280,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0
    | ~ spl4_62 ),
    inference(resolution,[],[f7174,f37])).

fof(f7174,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f7172])).

fof(f7415,plain,
    ( spl4_63
    | ~ spl4_13
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f7279,f7172,f345,f7412])).

fof(f345,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f7279,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_13
    | ~ spl4_62 ),
    inference(resolution,[],[f7174,f346])).

fof(f346,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | r1_tarski(sK2,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f345])).

fof(f7175,plain,
    ( spl4_62
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f7075,f6975,f7172])).

fof(f7075,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl4_61 ),
    inference(superposition,[],[f457,f6977])).

fof(f457,plain,(
    ! [X10,X11,X9] : r1_tarski(k2_zfmisc_1(X11,k3_xboole_0(X10,X9)),k2_zfmisc_1(X11,X9)) ),
    inference(superposition,[],[f126,f110])).

fof(f126,plain,(
    ! [X10,X8,X9] : r1_tarski(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X8,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f65,f35])).

fof(f7047,plain,
    ( spl4_61
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f6878,f5267,f6975])).

fof(f5267,plain,
    ( spl4_38
  <=> ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f6878,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl4_38 ),
    inference(superposition,[],[f149,f5268])).

fof(f5268,plain,
    ( ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f5267])).

fof(f149,plain,(
    ! [X14,X12,X13,X11] : k3_xboole_0(k2_zfmisc_1(X11,X13),k2_zfmisc_1(k2_xboole_0(X11,X12),X14)) = k2_zfmisc_1(X11,k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f38,f29])).

fof(f6357,plain,
    ( spl4_52
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f1368,f312,f5484])).

fof(f312,plain,
    ( spl4_11
  <=> ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1368,plain,
    ( ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3)))
    | ~ spl4_11 ),
    inference(superposition,[],[f69,f313])).

fof(f313,plain,
    ( ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f312])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f29,f27])).

fof(f6210,plain,
    ( spl4_38
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1296,f272,f5267])).

fof(f272,plain,
    ( spl4_9
  <=> ! [X0] : k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1296,plain,
    ( ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3))
    | ~ spl4_9 ),
    inference(superposition,[],[f69,f273])).

fof(f273,plain,
    ( ! [X0] : k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f272])).

fof(f481,plain,
    ( spl4_20
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f471,f463,f61,f478])).

fof(f61,plain,
    ( spl4_5
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f471,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f63,f465])).

fof(f63,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f469,plain,
    ( spl4_18
    | spl4_19
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f144,f61,f467,f463])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
        | r1_tarski(sK3,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl4_5 ),
    inference(superposition,[],[f37,f63])).

fof(f347,plain,
    ( spl4_12
    | spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f141,f61,f345,f341])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | r1_tarski(sK2,X0)
        | k1_xboole_0 = sK3 )
    | ~ spl4_5 ),
    inference(superposition,[],[f36,f63])).

fof(f314,plain,
    ( spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f119,f61,f312])).

fof(f119,plain,
    ( ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f35,f63])).

fof(f274,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f100,f61,f272])).

fof(f100,plain,
    ( ! [X0] : k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f34,f63])).

fof(f64,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f61])).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f59,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f24,f56,f52])).

fof(f24,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.54  % (4113)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (4110)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (4114)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (4119)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (4103)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (4106)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (4098)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (4105)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (4118)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (4102)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (4111)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (4108)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (4109)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (4097)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (4100)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (4101)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.57  % (4116)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.57  % (4117)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.60  % (4095)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.61  % (4120)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.61  % (4104)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.61  % (4112)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.61  % (4096)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.61  % (4115)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.82/0.63  % (4107)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 2.14/0.63  % (4099)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 4.03/0.92  % (4095)Time limit reached!
% 4.03/0.92  % (4095)------------------------------
% 4.03/0.92  % (4095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.92  % (4095)Termination reason: Time limit
% 4.03/0.92  % (4095)Termination phase: Saturation
% 4.03/0.92  
% 4.03/0.92  % (4095)Memory used [KB]: 14200
% 4.03/0.92  % (4095)Time elapsed: 0.500 s
% 4.03/0.92  % (4095)------------------------------
% 4.03/0.92  % (4095)------------------------------
% 4.45/0.93  % (4108)Time limit reached!
% 4.45/0.93  % (4108)------------------------------
% 4.45/0.93  % (4108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (4108)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (4108)Memory used [KB]: 11001
% 4.45/0.93  % (4108)Time elapsed: 0.501 s
% 4.45/0.93  % (4108)------------------------------
% 4.45/0.93  % (4108)------------------------------
% 5.21/1.03  % (4101)Time limit reached!
% 5.21/1.03  % (4101)------------------------------
% 5.21/1.03  % (4101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.21/1.04  % (4101)Termination reason: Time limit
% 5.21/1.04  % (4101)Termination phase: Saturation
% 5.21/1.04  
% 5.21/1.04  % (4101)Memory used [KB]: 14328
% 5.21/1.04  % (4101)Time elapsed: 0.600 s
% 5.21/1.04  % (4101)------------------------------
% 5.21/1.04  % (4101)------------------------------
% 6.48/1.20  % (4109)Time limit reached!
% 6.48/1.20  % (4109)------------------------------
% 6.48/1.20  % (4109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.48/1.20  % (4109)Termination reason: Time limit
% 6.48/1.20  % (4109)Termination phase: Saturation
% 6.48/1.20  
% 6.48/1.20  % (4109)Memory used [KB]: 20340
% 6.48/1.20  % (4109)Time elapsed: 0.500 s
% 6.48/1.20  % (4109)------------------------------
% 6.48/1.20  % (4109)------------------------------
% 7.52/1.33  % (4097)Refutation found. Thanks to Tanya!
% 7.52/1.33  % SZS status Theorem for theBenchmark
% 7.52/1.33  % SZS output start Proof for theBenchmark
% 7.52/1.33  fof(f13898,plain,(
% 7.52/1.33    $false),
% 7.52/1.33    inference(avatar_sat_refutation,[],[f45,f50,f59,f64,f274,f314,f347,f469,f481,f6210,f6357,f7047,f7175,f7415,f7610,f7666,f7729,f7874,f8246,f8254,f12136,f12260,f12367,f12370,f12371,f12373,f12665,f12824,f12831,f13309,f13324,f13414,f13593,f13744,f13820,f13885])).
% 7.52/1.33  fof(f13885,plain,(
% 7.52/1.33    spl4_1 | ~spl4_119 | ~spl4_143),
% 7.52/1.33    inference(avatar_contradiction_clause,[],[f13884])).
% 7.52/1.33  fof(f13884,plain,(
% 7.52/1.33    $false | (spl4_1 | ~spl4_119 | ~spl4_143)),
% 7.52/1.33    inference(subsumption_resolution,[],[f13883,f44])).
% 7.52/1.33  fof(f44,plain,(
% 7.52/1.33    k1_xboole_0 != sK0 | spl4_1),
% 7.52/1.33    inference(avatar_component_clause,[],[f42])).
% 7.52/1.33  fof(f42,plain,(
% 7.52/1.33    spl4_1 <=> k1_xboole_0 = sK0),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 7.52/1.33  fof(f13883,plain,(
% 7.52/1.33    k1_xboole_0 = sK0 | (~spl4_119 | ~spl4_143)),
% 7.52/1.33    inference(subsumption_resolution,[],[f13827,f12664])).
% 7.52/1.33  fof(f12664,plain,(
% 7.52/1.33    r1_tarski(sK0,k1_xboole_0) | ~spl4_119),
% 7.52/1.33    inference(avatar_component_clause,[],[f12662])).
% 7.52/1.33  fof(f12662,plain,(
% 7.52/1.33    spl4_119 <=> r1_tarski(sK0,k1_xboole_0)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).
% 7.52/1.33  fof(f13827,plain,(
% 7.52/1.33    ~r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 | ~spl4_143),
% 7.52/1.33    inference(superposition,[],[f72,f13759])).
% 7.52/1.33  fof(f13759,plain,(
% 7.52/1.33    sK0 = k2_xboole_0(k1_xboole_0,sK0) | ~spl4_143),
% 7.52/1.33    inference(avatar_component_clause,[],[f13757])).
% 7.52/1.33  fof(f13757,plain,(
% 7.52/1.33    spl4_143 <=> sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 7.52/1.33  fof(f72,plain,(
% 7.52/1.33    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 7.52/1.33    inference(resolution,[],[f32,f26])).
% 7.52/1.33  fof(f26,plain,(
% 7.52/1.33    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.52/1.33    inference(cnf_transformation,[],[f7])).
% 7.52/1.33  fof(f7,axiom,(
% 7.52/1.33    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.52/1.33  fof(f32,plain,(
% 7.52/1.33    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 7.52/1.33    inference(cnf_transformation,[],[f20])).
% 7.52/1.33  fof(f20,plain,(
% 7.52/1.33    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.52/1.33    inference(flattening,[],[f19])).
% 7.52/1.33  fof(f19,plain,(
% 7.52/1.33    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.52/1.33    inference(nnf_transformation,[],[f4])).
% 7.52/1.33  fof(f4,axiom,(
% 7.52/1.33    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.52/1.33  fof(f13820,plain,(
% 7.52/1.33    spl4_143 | ~spl4_141),
% 7.52/1.33    inference(avatar_split_clause,[],[f13748,f13741,f13757])).
% 7.52/1.33  fof(f13741,plain,(
% 7.52/1.33    spl4_141 <=> r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 7.52/1.33  fof(f13748,plain,(
% 7.52/1.33    sK0 = k2_xboole_0(k1_xboole_0,sK0) | ~spl4_141),
% 7.52/1.33    inference(subsumption_resolution,[],[f13747,f65])).
% 7.52/1.33  fof(f65,plain,(
% 7.52/1.33    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 7.52/1.33    inference(superposition,[],[f26,f27])).
% 7.52/1.33  fof(f27,plain,(
% 7.52/1.33    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.52/1.33    inference(cnf_transformation,[],[f1])).
% 7.52/1.33  fof(f1,axiom,(
% 7.52/1.33    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 7.52/1.33  fof(f13747,plain,(
% 7.52/1.33    ~r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK0)) | sK0 = k2_xboole_0(k1_xboole_0,sK0) | ~spl4_141),
% 7.52/1.33    inference(resolution,[],[f13743,f32])).
% 7.52/1.33  fof(f13743,plain,(
% 7.52/1.33    r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0) | ~spl4_141),
% 7.52/1.33    inference(avatar_component_clause,[],[f13741])).
% 7.52/1.33  fof(f13744,plain,(
% 7.52/1.33    spl4_141 | ~spl4_78 | ~spl4_140),
% 7.52/1.33    inference(avatar_split_clause,[],[f13732,f13590,f8244,f13741])).
% 7.52/1.33  fof(f8244,plain,(
% 7.52/1.33    spl4_78 <=> ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(X5,sK0))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 7.52/1.33  fof(f13590,plain,(
% 7.52/1.33    spl4_140 <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).
% 7.52/1.33  fof(f13732,plain,(
% 7.52/1.33    r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0) | (~spl4_78 | ~spl4_140)),
% 7.52/1.33    inference(subsumption_resolution,[],[f13679,f39])).
% 7.52/1.33  fof(f39,plain,(
% 7.52/1.33    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.52/1.33    inference(equality_resolution,[],[f31])).
% 7.52/1.33  fof(f31,plain,(
% 7.52/1.33    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.52/1.33    inference(cnf_transformation,[],[f20])).
% 7.52/1.33  fof(f13679,plain,(
% 7.52/1.33    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(k2_xboole_0(k1_xboole_0,sK0),sK0) | (~spl4_78 | ~spl4_140)),
% 7.52/1.33    inference(superposition,[],[f8245,f13592])).
% 7.52/1.33  fof(f13592,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1) | ~spl4_140),
% 7.52/1.33    inference(avatar_component_clause,[],[f13590])).
% 7.52/1.33  fof(f8245,plain,(
% 7.52/1.33    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(X5,sK0)) ) | ~spl4_78),
% 7.52/1.33    inference(avatar_component_clause,[],[f8244])).
% 7.52/1.33  fof(f13593,plain,(
% 7.52/1.33    spl4_140 | ~spl4_129 | ~spl4_137),
% 7.52/1.33    inference(avatar_split_clause,[],[f13498,f13411,f12808,f13590])).
% 7.52/1.33  fof(f12808,plain,(
% 7.52/1.33    spl4_129 <=> ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).
% 7.52/1.33  fof(f13411,plain,(
% 7.52/1.33    spl4_137 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).
% 7.52/1.33  fof(f13498,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1) | (~spl4_129 | ~spl4_137)),
% 7.52/1.33    inference(forward_demodulation,[],[f13000,f13413])).
% 7.52/1.33  fof(f13413,plain,(
% 7.52/1.33    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~spl4_137),
% 7.52/1.33    inference(avatar_component_clause,[],[f13411])).
% 7.52/1.33  fof(f13000,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1) | ~spl4_129),
% 7.52/1.33    inference(forward_demodulation,[],[f12929,f1762])).
% 7.52/1.33  fof(f1762,plain,(
% 7.52/1.33    ( ! [X8,X7,X9] : (k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_zfmisc_1(X7,k2_xboole_0(X9,X8))) )),
% 7.52/1.33    inference(superposition,[],[f121,f35])).
% 7.52/1.33  fof(f35,plain,(
% 7.52/1.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 7.52/1.33    inference(cnf_transformation,[],[f9])).
% 7.52/1.33  fof(f9,axiom,(
% 7.52/1.33    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 7.52/1.33  fof(f121,plain,(
% 7.52/1.33    ( ! [X6,X7,X5] : (k2_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X5,X6)) = k2_zfmisc_1(X5,k2_xboole_0(X6,X7))) )),
% 7.52/1.33    inference(superposition,[],[f35,f27])).
% 7.52/1.33  fof(f12929,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k2_xboole_0(sK1,k1_xboole_0)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK0),sK1) | ~spl4_129),
% 7.52/1.33    inference(superposition,[],[f35,f12809])).
% 7.52/1.33  fof(f12809,plain,(
% 7.52/1.33    ( ! [X1] : (k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) | ~spl4_129),
% 7.52/1.33    inference(avatar_component_clause,[],[f12808])).
% 7.52/1.33  fof(f13414,plain,(
% 7.52/1.33    spl4_137 | ~spl4_136),
% 7.52/1.33    inference(avatar_split_clause,[],[f13339,f13321,f13411])).
% 7.52/1.33  fof(f13321,plain,(
% 7.52/1.33    spl4_136 <=> sK1 = k3_xboole_0(k1_xboole_0,sK1)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).
% 7.52/1.33  fof(f13339,plain,(
% 7.52/1.33    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~spl4_136),
% 7.52/1.33    inference(superposition,[],[f94,f13323])).
% 7.52/1.33  fof(f13323,plain,(
% 7.52/1.33    sK1 = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_136),
% 7.52/1.33    inference(avatar_component_clause,[],[f13321])).
% 7.52/1.33  fof(f94,plain,(
% 7.52/1.33    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.52/1.33    inference(forward_demodulation,[],[f76,f29])).
% 7.52/1.33  fof(f29,plain,(
% 7.52/1.33    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.52/1.33    inference(cnf_transformation,[],[f5])).
% 7.52/1.33  fof(f5,axiom,(
% 7.52/1.33    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 7.52/1.33  fof(f76,plain,(
% 7.52/1.33    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.52/1.33    inference(superposition,[],[f33,f25])).
% 7.52/1.33  fof(f25,plain,(
% 7.52/1.33    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.52/1.33    inference(cnf_transformation,[],[f13])).
% 7.52/1.33  fof(f13,plain,(
% 7.52/1.33    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.52/1.33    inference(rectify,[],[f3])).
% 7.52/1.33  fof(f3,axiom,(
% 7.52/1.33    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 7.52/1.33  fof(f33,plain,(
% 7.52/1.33    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.52/1.33    inference(cnf_transformation,[],[f6])).
% 7.52/1.33  fof(f6,axiom,(
% 7.52/1.33    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 7.52/1.33  fof(f13324,plain,(
% 7.52/1.33    spl4_136 | ~spl4_134),
% 7.52/1.33    inference(avatar_split_clause,[],[f13316,f13306,f13321])).
% 7.52/1.33  fof(f13306,plain,(
% 7.52/1.33    spl4_134 <=> r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 7.52/1.33  fof(f13316,plain,(
% 7.52/1.33    sK1 = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_134),
% 7.52/1.33    inference(subsumption_resolution,[],[f13315,f166])).
% 7.52/1.33  fof(f166,plain,(
% 7.52/1.33    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 7.52/1.33    inference(superposition,[],[f116,f28])).
% 7.52/1.33  fof(f28,plain,(
% 7.52/1.33    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.52/1.33    inference(cnf_transformation,[],[f2])).
% 7.52/1.33  fof(f2,axiom,(
% 7.52/1.33    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.52/1.33  fof(f116,plain,(
% 7.52/1.33    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) )),
% 7.52/1.33    inference(superposition,[],[f65,f94])).
% 7.52/1.33  fof(f13315,plain,(
% 7.52/1.33    ~r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1) | sK1 = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_134),
% 7.52/1.33    inference(resolution,[],[f13308,f32])).
% 7.52/1.33  fof(f13308,plain,(
% 7.52/1.33    r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1)) | ~spl4_134),
% 7.52/1.33    inference(avatar_component_clause,[],[f13306])).
% 7.52/1.33  fof(f13309,plain,(
% 7.52/1.33    spl4_134 | ~spl4_80 | ~spl4_132),
% 7.52/1.33    inference(avatar_split_clause,[],[f13283,f12828,f8252,f13306])).
% 7.52/1.33  fof(f8252,plain,(
% 7.52/1.33    spl4_80 <=> ! [X6] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6)) | r1_tarski(sK1,X6))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 7.52/1.33  fof(f12828,plain,(
% 7.52/1.33    spl4_132 <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(k1_xboole_0,sK1))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).
% 7.52/1.33  fof(f13283,plain,(
% 7.52/1.33    r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1)) | (~spl4_80 | ~spl4_132)),
% 7.52/1.33    inference(subsumption_resolution,[],[f13227,f39])).
% 7.52/1.33  fof(f13227,plain,(
% 7.52/1.33    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(sK1,k3_xboole_0(k1_xboole_0,sK1)) | (~spl4_80 | ~spl4_132)),
% 7.52/1.33    inference(superposition,[],[f8253,f12830])).
% 7.52/1.33  fof(f12830,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(k1_xboole_0,sK1)) | ~spl4_132),
% 7.52/1.33    inference(avatar_component_clause,[],[f12828])).
% 7.52/1.33  fof(f8253,plain,(
% 7.52/1.33    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6)) | r1_tarski(sK1,X6)) ) | ~spl4_80),
% 7.52/1.33    inference(avatar_component_clause,[],[f8252])).
% 7.52/1.33  fof(f12831,plain,(
% 7.52/1.33    spl4_132 | ~spl4_12 | ~spl4_20 | ~spl4_61),
% 7.52/1.33    inference(avatar_split_clause,[],[f12778,f6975,f478,f341,f12828])).
% 7.52/1.33  fof(f341,plain,(
% 7.52/1.33    spl4_12 <=> k1_xboole_0 = sK3),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 7.52/1.33  fof(f478,plain,(
% 7.52/1.33    spl4_20 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 7.52/1.33  fof(f6975,plain,(
% 7.52/1.33    spl4_61 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 7.52/1.33  fof(f12778,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(k1_xboole_0,sK1)) | (~spl4_12 | ~spl4_20 | ~spl4_61)),
% 7.52/1.33    inference(forward_demodulation,[],[f12777,f28])).
% 7.52/1.33  fof(f12777,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k1_xboole_0)) | (~spl4_12 | ~spl4_20 | ~spl4_61)),
% 7.52/1.33    inference(forward_demodulation,[],[f12408,f343])).
% 7.52/1.33  fof(f343,plain,(
% 7.52/1.33    k1_xboole_0 = sK3 | ~spl4_12),
% 7.52/1.33    inference(avatar_component_clause,[],[f341])).
% 7.52/1.33  fof(f12408,plain,(
% 7.52/1.33    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl4_20 | ~spl4_61)),
% 7.52/1.33    inference(backward_demodulation,[],[f6977,f480])).
% 7.52/1.33  fof(f480,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | ~spl4_20),
% 7.52/1.33    inference(avatar_component_clause,[],[f478])).
% 7.52/1.33  fof(f6977,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~spl4_61),
% 7.52/1.33    inference(avatar_component_clause,[],[f6975])).
% 7.52/1.33  fof(f12824,plain,(
% 7.52/1.33    spl4_129 | ~spl4_12 | ~spl4_20),
% 7.52/1.33    inference(avatar_split_clause,[],[f12793,f478,f341,f12808])).
% 7.52/1.33  fof(f12793,plain,(
% 7.52/1.33    ( ! [X1] : (k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) | (~spl4_12 | ~spl4_20)),
% 7.52/1.33    inference(forward_demodulation,[],[f12422,f343])).
% 7.52/1.33  fof(f12422,plain,(
% 7.52/1.33    ( ! [X1] : (k2_zfmisc_1(k2_xboole_0(X1,sK0),sK1) = k2_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(k1_xboole_0,sK3))) ) | ~spl4_20),
% 7.52/1.33    inference(superposition,[],[f34,f480])).
% 7.52/1.33  fof(f34,plain,(
% 7.52/1.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 7.52/1.33    inference(cnf_transformation,[],[f9])).
% 7.52/1.33  fof(f12665,plain,(
% 7.52/1.33    spl4_119 | spl4_2 | ~spl4_18 | ~spl4_116),
% 7.52/1.33    inference(avatar_split_clause,[],[f12658,f12257,f463,f47,f12662])).
% 7.52/1.33  fof(f47,plain,(
% 7.52/1.33    spl4_2 <=> k1_xboole_0 = sK1),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 7.52/1.33  fof(f463,plain,(
% 7.52/1.33    spl4_18 <=> k1_xboole_0 = sK2),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 7.52/1.33  fof(f12257,plain,(
% 7.52/1.33    spl4_116 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).
% 7.52/1.33  fof(f12658,plain,(
% 7.52/1.33    r1_tarski(sK0,k1_xboole_0) | (spl4_2 | ~spl4_18 | ~spl4_116)),
% 7.52/1.33    inference(forward_demodulation,[],[f12375,f465])).
% 7.52/1.33  fof(f465,plain,(
% 7.52/1.33    k1_xboole_0 = sK2 | ~spl4_18),
% 7.52/1.33    inference(avatar_component_clause,[],[f463])).
% 7.52/1.33  fof(f12375,plain,(
% 7.52/1.33    r1_tarski(sK0,sK2) | (spl4_2 | ~spl4_116)),
% 7.52/1.33    inference(subsumption_resolution,[],[f12362,f49])).
% 7.52/1.33  fof(f49,plain,(
% 7.52/1.33    k1_xboole_0 != sK1 | spl4_2),
% 7.52/1.33    inference(avatar_component_clause,[],[f47])).
% 7.52/1.33  fof(f12362,plain,(
% 7.52/1.33    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1 | ~spl4_116),
% 7.52/1.33    inference(resolution,[],[f12259,f36])).
% 7.52/1.33  fof(f36,plain,(
% 7.52/1.33    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 7.52/1.33    inference(cnf_transformation,[],[f16])).
% 7.52/1.33  fof(f16,plain,(
% 7.52/1.33    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 7.52/1.33    inference(ennf_transformation,[],[f8])).
% 7.52/1.33  fof(f8,axiom,(
% 7.52/1.33    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 7.52/1.33  fof(f12259,plain,(
% 7.52/1.33    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl4_116),
% 7.52/1.33    inference(avatar_component_clause,[],[f12257])).
% 7.52/1.33  fof(f12373,plain,(
% 7.52/1.33    k1_xboole_0 != sK2 | sK0 != sK2 | k1_xboole_0 = sK0),
% 7.52/1.33    introduced(theory_tautology_sat_conflict,[])).
% 7.52/1.33  fof(f12371,plain,(
% 7.52/1.33    k1_xboole_0 != sK3 | sK1 != sK3 | k1_xboole_0 = sK1),
% 7.52/1.33    introduced(theory_tautology_sat_conflict,[])).
% 7.52/1.33  fof(f12370,plain,(
% 7.52/1.33    spl4_2 | spl4_68 | ~spl4_116),
% 7.52/1.33    inference(avatar_contradiction_clause,[],[f12369])).
% 7.52/1.33  fof(f12369,plain,(
% 7.52/1.33    $false | (spl4_2 | spl4_68 | ~spl4_116)),
% 7.52/1.33    inference(subsumption_resolution,[],[f12368,f49])).
% 7.52/1.33  fof(f12368,plain,(
% 7.52/1.33    k1_xboole_0 = sK1 | (spl4_68 | ~spl4_116)),
% 7.52/1.33    inference(subsumption_resolution,[],[f12362,f7728])).
% 7.52/1.33  fof(f7728,plain,(
% 7.52/1.33    ~r1_tarski(sK0,sK2) | spl4_68),
% 7.52/1.33    inference(avatar_component_clause,[],[f7726])).
% 7.52/1.33  fof(f7726,plain,(
% 7.52/1.33    spl4_68 <=> r1_tarski(sK0,sK2)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 7.52/1.33  fof(f12367,plain,(
% 7.52/1.33    ~spl4_19 | spl4_67 | ~spl4_116),
% 7.52/1.33    inference(avatar_contradiction_clause,[],[f12366])).
% 7.52/1.33  fof(f12366,plain,(
% 7.52/1.33    $false | (~spl4_19 | spl4_67 | ~spl4_116)),
% 7.52/1.33    inference(subsumption_resolution,[],[f12361,f7665])).
% 7.52/1.33  fof(f7665,plain,(
% 7.52/1.33    ~r1_tarski(sK3,sK1) | spl4_67),
% 7.52/1.33    inference(avatar_component_clause,[],[f7663])).
% 7.52/1.33  fof(f7663,plain,(
% 7.52/1.33    spl4_67 <=> r1_tarski(sK3,sK1)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 7.52/1.33  fof(f12361,plain,(
% 7.52/1.33    r1_tarski(sK3,sK1) | (~spl4_19 | ~spl4_116)),
% 7.52/1.33    inference(resolution,[],[f12259,f468])).
% 7.52/1.33  fof(f468,plain,(
% 7.52/1.33    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | r1_tarski(sK3,X0)) ) | ~spl4_19),
% 7.52/1.33    inference(avatar_component_clause,[],[f467])).
% 7.52/1.33  fof(f467,plain,(
% 7.52/1.33    spl4_19 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | r1_tarski(sK3,X0))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 7.52/1.33  fof(f12260,plain,(
% 7.52/1.33    spl4_116 | ~spl4_115),
% 7.52/1.33    inference(avatar_split_clause,[],[f12160,f12068,f12257])).
% 7.52/1.33  fof(f12068,plain,(
% 7.52/1.33    spl4_115 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).
% 7.52/1.33  fof(f12160,plain,(
% 7.52/1.33    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl4_115),
% 7.52/1.33    inference(superposition,[],[f306,f12070])).
% 7.52/1.33  fof(f12070,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl4_115),
% 7.52/1.33    inference(avatar_component_clause,[],[f12068])).
% 7.52/1.33  fof(f306,plain,(
% 7.52/1.33    ( ! [X10,X11,X9] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X10,X9),X11),k2_zfmisc_1(X9,X11))) )),
% 7.52/1.33    inference(superposition,[],[f105,f110])).
% 7.52/1.33  fof(f110,plain,(
% 7.52/1.33    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 7.52/1.33    inference(superposition,[],[f94,f28])).
% 7.52/1.33  fof(f105,plain,(
% 7.52/1.33    ( ! [X6,X8,X7] : (r1_tarski(k2_zfmisc_1(X8,X7),k2_zfmisc_1(k2_xboole_0(X6,X8),X7))) )),
% 7.52/1.33    inference(superposition,[],[f65,f34])).
% 7.52/1.33  fof(f12136,plain,(
% 7.52/1.33    spl4_115 | ~spl4_52),
% 7.52/1.33    inference(avatar_split_clause,[],[f11971,f5484,f12068])).
% 7.52/1.33  fof(f5484,plain,(
% 7.52/1.33    spl4_52 <=> ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3)))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 7.52/1.33  fof(f11971,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl4_52),
% 7.52/1.33    inference(superposition,[],[f154,f5485])).
% 7.52/1.33  fof(f5485,plain,(
% 7.52/1.33    ( ! [X5] : (k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3)))) ) | ~spl4_52),
% 7.52/1.33    inference(avatar_component_clause,[],[f5484])).
% 7.52/1.33  fof(f154,plain,(
% 7.52/1.33    ( ! [X14,X12,X13,X11] : (k3_xboole_0(k2_zfmisc_1(X13,X11),k2_zfmisc_1(X14,k2_xboole_0(X11,X12))) = k2_zfmisc_1(k3_xboole_0(X13,X14),X11)) )),
% 7.52/1.33    inference(superposition,[],[f38,f29])).
% 7.52/1.33  fof(f38,plain,(
% 7.52/1.33    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 7.52/1.33    inference(cnf_transformation,[],[f10])).
% 7.52/1.33  fof(f10,axiom,(
% 7.52/1.33    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 7.52/1.33  fof(f8254,plain,(
% 7.52/1.33    spl4_80 | spl4_1 | ~spl4_22),
% 7.52/1.33    inference(avatar_split_clause,[],[f8201,f588,f42,f8252])).
% 7.52/1.33  fof(f588,plain,(
% 7.52/1.33    spl4_22 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 7.52/1.33  fof(f8201,plain,(
% 7.52/1.33    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6)) | r1_tarski(sK1,X6)) ) | (spl4_1 | ~spl4_22)),
% 7.52/1.33    inference(subsumption_resolution,[],[f8161,f44])).
% 7.52/1.33  fof(f8161,plain,(
% 7.52/1.33    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(sK0,X6)) | r1_tarski(sK1,X6) | k1_xboole_0 = sK0) ) | ~spl4_22),
% 7.52/1.33    inference(superposition,[],[f37,f589])).
% 7.52/1.33  fof(f589,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl4_22),
% 7.52/1.33    inference(avatar_component_clause,[],[f588])).
% 7.52/1.33  fof(f37,plain,(
% 7.52/1.33    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 7.52/1.33    inference(cnf_transformation,[],[f16])).
% 7.52/1.33  fof(f8246,plain,(
% 7.52/1.33    spl4_78 | spl4_2 | ~spl4_22),
% 7.52/1.33    inference(avatar_split_clause,[],[f8200,f588,f47,f8244])).
% 7.52/1.33  fof(f8200,plain,(
% 7.52/1.33    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(X5,sK0)) ) | (spl4_2 | ~spl4_22)),
% 7.52/1.33    inference(subsumption_resolution,[],[f8160,f49])).
% 7.52/1.33  fof(f8160,plain,(
% 7.52/1.33    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(X5,sK0) | k1_xboole_0 = sK1) ) | ~spl4_22),
% 7.52/1.33    inference(superposition,[],[f36,f589])).
% 7.52/1.33  fof(f7874,plain,(
% 7.52/1.33    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 7.52/1.33    introduced(theory_tautology_sat_conflict,[])).
% 7.52/1.33  fof(f7729,plain,(
% 7.52/1.33    spl4_3 | ~spl4_68 | ~spl4_63),
% 7.52/1.33    inference(avatar_split_clause,[],[f7659,f7412,f7726,f52])).
% 7.52/1.33  fof(f52,plain,(
% 7.52/1.33    spl4_3 <=> sK0 = sK2),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 7.52/1.33  fof(f7412,plain,(
% 7.52/1.33    spl4_63 <=> r1_tarski(sK2,sK0)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 7.52/1.33  fof(f7659,plain,(
% 7.52/1.33    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_63),
% 7.52/1.33    inference(resolution,[],[f7414,f32])).
% 7.52/1.33  fof(f7414,plain,(
% 7.52/1.33    r1_tarski(sK2,sK0) | ~spl4_63),
% 7.52/1.33    inference(avatar_component_clause,[],[f7412])).
% 7.52/1.33  fof(f7666,plain,(
% 7.52/1.33    ~spl4_67 | spl4_4 | ~spl4_66),
% 7.52/1.33    inference(avatar_split_clause,[],[f7661,f7607,f56,f7663])).
% 7.52/1.33  fof(f56,plain,(
% 7.52/1.33    spl4_4 <=> sK1 = sK3),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 7.52/1.33  fof(f7607,plain,(
% 7.52/1.33    spl4_66 <=> r1_tarski(sK1,sK3)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 7.52/1.33  fof(f7661,plain,(
% 7.52/1.33    ~r1_tarski(sK3,sK1) | (spl4_4 | ~spl4_66)),
% 7.52/1.33    inference(subsumption_resolution,[],[f7660,f58])).
% 7.52/1.33  fof(f58,plain,(
% 7.52/1.33    sK1 != sK3 | spl4_4),
% 7.52/1.33    inference(avatar_component_clause,[],[f56])).
% 7.52/1.33  fof(f7660,plain,(
% 7.52/1.33    ~r1_tarski(sK3,sK1) | sK1 = sK3 | ~spl4_66),
% 7.52/1.33    inference(resolution,[],[f7609,f32])).
% 7.52/1.33  fof(f7609,plain,(
% 7.52/1.33    r1_tarski(sK1,sK3) | ~spl4_66),
% 7.52/1.33    inference(avatar_component_clause,[],[f7607])).
% 7.52/1.33  fof(f7610,plain,(
% 7.52/1.33    spl4_66 | spl4_1 | ~spl4_62),
% 7.52/1.33    inference(avatar_split_clause,[],[f7282,f7172,f42,f7607])).
% 7.52/1.33  fof(f7172,plain,(
% 7.52/1.33    spl4_62 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 7.52/1.33  fof(f7282,plain,(
% 7.52/1.33    r1_tarski(sK1,sK3) | (spl4_1 | ~spl4_62)),
% 7.52/1.33    inference(subsumption_resolution,[],[f7280,f44])).
% 7.52/1.33  fof(f7280,plain,(
% 7.52/1.33    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0 | ~spl4_62),
% 7.52/1.33    inference(resolution,[],[f7174,f37])).
% 7.52/1.33  fof(f7174,plain,(
% 7.52/1.33    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl4_62),
% 7.52/1.33    inference(avatar_component_clause,[],[f7172])).
% 7.52/1.33  fof(f7415,plain,(
% 7.52/1.33    spl4_63 | ~spl4_13 | ~spl4_62),
% 7.52/1.33    inference(avatar_split_clause,[],[f7279,f7172,f345,f7412])).
% 7.52/1.33  fof(f345,plain,(
% 7.52/1.33    spl4_13 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | r1_tarski(sK2,X0))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 7.52/1.33  fof(f7279,plain,(
% 7.52/1.33    r1_tarski(sK2,sK0) | (~spl4_13 | ~spl4_62)),
% 7.52/1.33    inference(resolution,[],[f7174,f346])).
% 7.52/1.33  fof(f346,plain,(
% 7.52/1.33    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | r1_tarski(sK2,X0)) ) | ~spl4_13),
% 7.52/1.33    inference(avatar_component_clause,[],[f345])).
% 7.52/1.33  fof(f7175,plain,(
% 7.52/1.33    spl4_62 | ~spl4_61),
% 7.52/1.33    inference(avatar_split_clause,[],[f7075,f6975,f7172])).
% 7.52/1.33  fof(f7075,plain,(
% 7.52/1.33    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl4_61),
% 7.52/1.33    inference(superposition,[],[f457,f6977])).
% 7.52/1.33  fof(f457,plain,(
% 7.52/1.33    ( ! [X10,X11,X9] : (r1_tarski(k2_zfmisc_1(X11,k3_xboole_0(X10,X9)),k2_zfmisc_1(X11,X9))) )),
% 7.52/1.33    inference(superposition,[],[f126,f110])).
% 7.52/1.33  fof(f126,plain,(
% 7.52/1.33    ( ! [X10,X8,X9] : (r1_tarski(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X8,k2_xboole_0(X9,X10)))) )),
% 7.52/1.33    inference(superposition,[],[f65,f35])).
% 7.52/1.33  fof(f7047,plain,(
% 7.52/1.33    spl4_61 | ~spl4_38),
% 7.52/1.33    inference(avatar_split_clause,[],[f6878,f5267,f6975])).
% 7.52/1.33  fof(f5267,plain,(
% 7.52/1.33    spl4_38 <=> ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 7.52/1.33  fof(f6878,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~spl4_38),
% 7.52/1.33    inference(superposition,[],[f149,f5268])).
% 7.52/1.33  fof(f5268,plain,(
% 7.52/1.33    ( ! [X5] : (k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3))) ) | ~spl4_38),
% 7.52/1.33    inference(avatar_component_clause,[],[f5267])).
% 7.52/1.33  fof(f149,plain,(
% 7.52/1.33    ( ! [X14,X12,X13,X11] : (k3_xboole_0(k2_zfmisc_1(X11,X13),k2_zfmisc_1(k2_xboole_0(X11,X12),X14)) = k2_zfmisc_1(X11,k3_xboole_0(X13,X14))) )),
% 7.52/1.33    inference(superposition,[],[f38,f29])).
% 7.52/1.33  fof(f6357,plain,(
% 7.52/1.33    spl4_52 | ~spl4_11),
% 7.52/1.33    inference(avatar_split_clause,[],[f1368,f312,f5484])).
% 7.52/1.33  fof(f312,plain,(
% 7.52/1.33    spl4_11 <=> ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 7.52/1.33  fof(f1368,plain,(
% 7.52/1.33    ( ! [X5] : (k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3)))) ) | ~spl4_11),
% 7.52/1.33    inference(superposition,[],[f69,f313])).
% 7.52/1.33  fof(f313,plain,(
% 7.52/1.33    ( ! [X0] : (k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_11),
% 7.52/1.33    inference(avatar_component_clause,[],[f312])).
% 7.52/1.33  fof(f69,plain,(
% 7.52/1.33    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 7.52/1.33    inference(superposition,[],[f29,f27])).
% 7.52/1.33  fof(f6210,plain,(
% 7.52/1.33    spl4_38 | ~spl4_9),
% 7.52/1.33    inference(avatar_split_clause,[],[f1296,f272,f5267])).
% 7.52/1.33  fof(f272,plain,(
% 7.52/1.33    spl4_9 <=> ! [X0] : k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 7.52/1.33  fof(f1296,plain,(
% 7.52/1.33    ( ! [X5] : (k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3))) ) | ~spl4_9),
% 7.52/1.33    inference(superposition,[],[f69,f273])).
% 7.52/1.33  fof(f273,plain,(
% 7.52/1.33    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_9),
% 7.52/1.33    inference(avatar_component_clause,[],[f272])).
% 7.52/1.33  fof(f481,plain,(
% 7.52/1.33    spl4_20 | ~spl4_5 | ~spl4_18),
% 7.52/1.33    inference(avatar_split_clause,[],[f471,f463,f61,f478])).
% 7.52/1.33  fof(f61,plain,(
% 7.52/1.33    spl4_5 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 7.52/1.33    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 7.52/1.33  fof(f471,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_5 | ~spl4_18)),
% 7.52/1.33    inference(backward_demodulation,[],[f63,f465])).
% 7.52/1.33  fof(f63,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~spl4_5),
% 7.52/1.33    inference(avatar_component_clause,[],[f61])).
% 7.52/1.33  fof(f469,plain,(
% 7.52/1.33    spl4_18 | spl4_19 | ~spl4_5),
% 7.52/1.33    inference(avatar_split_clause,[],[f144,f61,f467,f463])).
% 7.52/1.33  fof(f144,plain,(
% 7.52/1.33    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | r1_tarski(sK3,X0) | k1_xboole_0 = sK2) ) | ~spl4_5),
% 7.52/1.33    inference(superposition,[],[f37,f63])).
% 7.52/1.33  fof(f347,plain,(
% 7.52/1.33    spl4_12 | spl4_13 | ~spl4_5),
% 7.52/1.33    inference(avatar_split_clause,[],[f141,f61,f345,f341])).
% 7.52/1.33  fof(f141,plain,(
% 7.52/1.33    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | r1_tarski(sK2,X0) | k1_xboole_0 = sK3) ) | ~spl4_5),
% 7.52/1.33    inference(superposition,[],[f36,f63])).
% 7.52/1.33  fof(f314,plain,(
% 7.52/1.33    spl4_11 | ~spl4_5),
% 7.52/1.33    inference(avatar_split_clause,[],[f119,f61,f312])).
% 7.52/1.33  fof(f119,plain,(
% 7.52/1.33    ( ! [X0] : (k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_5),
% 7.52/1.33    inference(superposition,[],[f35,f63])).
% 7.52/1.33  fof(f274,plain,(
% 7.52/1.33    spl4_9 | ~spl4_5),
% 7.52/1.33    inference(avatar_split_clause,[],[f100,f61,f272])).
% 7.52/1.33  fof(f100,plain,(
% 7.52/1.33    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_5),
% 7.52/1.33    inference(superposition,[],[f34,f63])).
% 7.52/1.33  fof(f64,plain,(
% 7.52/1.33    spl4_5),
% 7.52/1.33    inference(avatar_split_clause,[],[f21,f61])).
% 7.52/1.33  fof(f21,plain,(
% 7.52/1.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 7.52/1.33    inference(cnf_transformation,[],[f18])).
% 7.52/1.33  fof(f18,plain,(
% 7.52/1.33    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 7.52/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).
% 7.52/1.33  fof(f17,plain,(
% 7.52/1.33    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 7.52/1.33    introduced(choice_axiom,[])).
% 7.52/1.33  fof(f15,plain,(
% 7.52/1.33    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.52/1.33    inference(flattening,[],[f14])).
% 7.52/1.33  fof(f14,plain,(
% 7.52/1.33    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.52/1.33    inference(ennf_transformation,[],[f12])).
% 7.52/1.33  fof(f12,negated_conjecture,(
% 7.52/1.33    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.52/1.33    inference(negated_conjecture,[],[f11])).
% 7.52/1.33  fof(f11,conjecture,(
% 7.52/1.33    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.52/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 7.52/1.33  fof(f59,plain,(
% 7.52/1.33    ~spl4_3 | ~spl4_4),
% 7.52/1.33    inference(avatar_split_clause,[],[f24,f56,f52])).
% 7.52/1.33  fof(f24,plain,(
% 7.52/1.33    sK1 != sK3 | sK0 != sK2),
% 7.52/1.33    inference(cnf_transformation,[],[f18])).
% 7.52/1.33  fof(f50,plain,(
% 7.52/1.33    ~spl4_2),
% 7.52/1.33    inference(avatar_split_clause,[],[f23,f47])).
% 7.52/1.33  fof(f23,plain,(
% 7.52/1.33    k1_xboole_0 != sK1),
% 7.52/1.33    inference(cnf_transformation,[],[f18])).
% 7.52/1.33  fof(f45,plain,(
% 7.52/1.33    ~spl4_1),
% 7.52/1.33    inference(avatar_split_clause,[],[f22,f42])).
% 7.52/1.33  fof(f22,plain,(
% 7.52/1.33    k1_xboole_0 != sK0),
% 7.52/1.33    inference(cnf_transformation,[],[f18])).
% 7.52/1.33  % SZS output end Proof for theBenchmark
% 7.52/1.33  % (4097)------------------------------
% 7.52/1.33  % (4097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.52/1.33  % (4097)Termination reason: Refutation
% 7.52/1.33  
% 7.52/1.33  % (4097)Memory used [KB]: 13432
% 7.52/1.33  % (4097)Time elapsed: 0.890 s
% 7.52/1.33  % (4097)------------------------------
% 7.52/1.33  % (4097)------------------------------
% 7.52/1.34  % (4094)Success in time 0.977 s
%------------------------------------------------------------------------------
