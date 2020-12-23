%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t139_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:01 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 122 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  184 ( 287 expanded)
%              Number of equality atoms :   45 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f50,f57,f64,f77,f86,f94,f116,f144,f150,f152,f163,f175])).

fof(f175,plain,
    ( spl5_19
    | spl5_21
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl5_19
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f173,f140])).

fof(f140,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_21
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f172,f134])).

fof(f134,plain,
    ( k1_xboole_0 != sK0
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_19
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f172,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl5_22 ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl5_22 ),
    inference(superposition,[],[f27,f162])).

fof(f162,plain,
    ( k2_zfmisc_1(sK1,sK0) = k1_xboole_0
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_22
  <=> k2_zfmisc_1(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',t113_zfmisc_1)).

fof(f163,plain,
    ( spl5_22
    | spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f155,f69,f48,f161])).

fof(f48,plain,
    ( spl5_3
  <=> ~ r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f69,plain,
    ( spl5_8
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f155,plain,
    ( k2_zfmisc_1(sK1,sK0) = k1_xboole_0
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f154,f49])).

fof(f49,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f154,plain,
    ( k2_zfmisc_1(sK1,sK0) = k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl5_8 ),
    inference(resolution,[],[f70,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',t138_zfmisc_1)).

fof(f70,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f152,plain,
    ( spl5_3
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f147,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',t2_xboole_1)).

fof(f147,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f143,f49])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f150,plain,
    ( spl5_9
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f148,f26])).

fof(f148,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2))
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f146,f36])).

fof(f36,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f146,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f143,f67])).

fof(f67,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_9
  <=> ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f144,plain,
    ( spl5_18
    | spl5_20
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f122,f114,f142,f136])).

fof(f136,plain,
    ( spl5_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f114,plain,
    ( spl5_16
  <=> k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f122,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_16 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_16 ),
    inference(superposition,[],[f27,f115])).

fof(f115,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl5_16
    | spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f108,f75,f48,f114])).

fof(f75,plain,
    ( spl5_10
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f108,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f25,f76])).

fof(f76,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,
    ( spl5_14
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f78,f62,f92])).

fof(f92,plain,
    ( spl5_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f62,plain,
    ( spl5_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f78,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl5_6 ),
    inference(resolution,[],[f33,f63])).

fof(f63,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',t6_boole)).

fof(f86,plain,
    ( spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f79,f62,f84])).

fof(f84,plain,
    ( spl5_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f78,f63])).

fof(f77,plain,
    ( spl5_8
    | spl5_10 ),
    inference(avatar_split_clause,[],[f21,f75,f69])).

fof(f21,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',t139_zfmisc_1)).

fof(f64,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(f57,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f55,plain,
    ( spl5_5
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f30,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t139_zfmisc_1.p',rc2_xboole_0)).

fof(f50,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f41,plain,
    ( spl5_1
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f23,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
