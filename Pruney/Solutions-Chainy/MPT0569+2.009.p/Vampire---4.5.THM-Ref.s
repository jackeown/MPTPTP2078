%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:27 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   90 (2072 expanded)
%              Number of leaves         :   11 ( 571 expanded)
%              Depth                    :   24
%              Number of atoms          :  176 (4603 expanded)
%              Number of equality atoms :   45 ( 993 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1050,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1011,f1002,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK9(X0,X2),X2),X0)
      | ~ sP8(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1002,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK1),sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f959,f997,f29])).

fof(f29,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f997,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f973,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f973,plain,(
    sP12(sK5(k2_relat_1(sK1),sK0),sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f961,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP12(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f961,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) ),
    inference(unit_resulting_resolution,[],[f949,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f949,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f948])).

fof(f948,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f941])).

fof(f941,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f25,f936])).

fof(f936,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(forward_demodulation,[],[f933,f463])).

fof(f463,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f411,f454])).

fof(f454,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f393,f453])).

fof(f453,plain,(
    k1_xboole_0 = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f352,f421])).

fof(f421,plain,(
    k2_relat_1(k1_xboole_0) = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f355,f358])).

fof(f358,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f110,f189,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f189,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f184,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP8(X2,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP8(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f184,plain,(
    ! [X0] : ~ sP8(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f176,f43])).

fof(f176,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f26,f90,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP3(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    ! [X0,X1] : ~ sP3(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f82,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f28])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f110,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f100,f71])).

fof(f100,plain,(
    ! [X0] : ~ sP8(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f82,f43])).

fof(f355,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f176,f189,f41])).

fof(f352,plain,(
    k1_xboole_0 = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f82,f189,f41])).

fof(f393,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f359,f358])).

fof(f359,plain,(
    k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f120,f189,f41])).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f115,f71])).

fof(f115,plain,(
    ! [X0] : ~ sP8(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f110,f43])).

fof(f411,plain,(
    k2_relat_1(k1_xboole_0) = k10_relat_1(sK1,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f356,f358])).

fof(f356,plain,(
    k10_relat_1(sK1,k2_relat_1(k1_xboole_0)) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f177,f189,f41])).

fof(f177,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f26,f114,f69])).

fof(f114,plain,(
    ! [X0,X1] : ~ sP3(X0,k2_relat_1(k1_xboole_0),X1) ),
    inference(unit_resulting_resolution,[],[f110,f31])).

fof(f933,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f669,f721])).

fof(f721,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f717,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f717,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f714,f454])).

fof(f714,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k1_xboole_0,X0),X0)
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f47,f100])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP8(sK7(X0,X1),X0)
      | r2_hidden(sK7(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f669,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f26,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f25,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f959,plain,(
    ! [X0] : ~ sP3(X0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f949,f198])).

fof(f198,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK0,sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(global_subsumption,[],[f26,f82,f196])).

fof(f196,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP3(X0,sK0,sK1)
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f70,f24])).

fof(f24,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ sP3(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1011,plain,(
    sP8(sK5(k2_relat_1(sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f998,f71])).

fof(f998,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f973,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (20567)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (20567)Refutation not found, incomplete strategy% (20567)------------------------------
% 0.20/0.46  % (20567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (20567)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (20567)Memory used [KB]: 10618
% 0.20/0.46  % (20567)Time elapsed: 0.053 s
% 0.20/0.46  % (20567)------------------------------
% 0.20/0.46  % (20567)------------------------------
% 0.20/0.47  % (20586)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (20559)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (20569)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (20570)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (20584)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (20558)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (20557)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (20563)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (20576)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (20583)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (20561)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (20579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (20560)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.54  % (20574)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.54  % (20579)Refutation not found, incomplete strategy% (20579)------------------------------
% 1.42/0.54  % (20579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (20579)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (20579)Memory used [KB]: 10746
% 1.42/0.54  % (20579)Time elapsed: 0.103 s
% 1.42/0.54  % (20579)------------------------------
% 1.42/0.54  % (20579)------------------------------
% 1.42/0.54  % (20562)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.54  % (20571)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.54  % (20581)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.54  % (20566)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  % (20578)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.55  % (20565)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (20580)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  % (20573)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (20575)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (20585)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (20568)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (20564)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (20568)Refutation not found, incomplete strategy% (20568)------------------------------
% 1.42/0.55  % (20568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (20568)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (20568)Memory used [KB]: 10618
% 1.42/0.55  % (20568)Time elapsed: 0.149 s
% 1.42/0.55  % (20568)------------------------------
% 1.42/0.55  % (20568)------------------------------
% 1.53/0.56  % (20577)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.57  % (20572)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.57  % (20582)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.58  % (20587)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.53/0.59  % (20581)Refutation found. Thanks to Tanya!
% 1.53/0.59  % SZS status Theorem for theBenchmark
% 1.53/0.59  % SZS output start Proof for theBenchmark
% 1.53/0.59  fof(f1050,plain,(
% 1.53/0.59    $false),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f1011,f1002,f43])).
% 1.53/0.59  fof(f43,plain,(
% 1.53/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK9(X0,X2),X2),X0) | ~sP8(X2,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f10])).
% 1.53/0.59  fof(f10,axiom,(
% 1.53/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.53/0.59  fof(f1002,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK1),sK0)),sK1)) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f959,f997,f29])).
% 1.53/0.59  fof(f29,plain,(
% 1.53/0.59    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP3(X3,X1,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f17])).
% 1.53/0.59  fof(f17,plain,(
% 1.53/0.59    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.53/0.59    inference(ennf_transformation,[],[f9])).
% 1.53/0.59  fof(f9,axiom,(
% 1.53/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.53/0.59  fof(f997,plain,(
% 1.53/0.59    r2_hidden(sK5(k2_relat_1(sK1),sK0),sK0)),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f973,f56])).
% 1.53/0.59  fof(f56,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (~sP12(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f1])).
% 1.53/0.59  fof(f1,axiom,(
% 1.53/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.53/0.59  fof(f973,plain,(
% 1.53/0.59    sP12(sK5(k2_relat_1(sK1),sK0),sK0,k2_relat_1(sK1))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f961,f73])).
% 1.53/0.59  fof(f73,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP12(X3,X1,X0)) )),
% 1.53/0.59    inference(equality_resolution,[],[f67])).
% 1.53/0.59  fof(f67,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (sP12(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.53/0.59    inference(definition_unfolding,[],[f58,f36])).
% 1.53/0.59  fof(f36,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f8])).
% 1.53/0.59  fof(f8,axiom,(
% 1.53/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.53/0.59  fof(f58,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (sP12(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.53/0.59    inference(cnf_transformation,[],[f1])).
% 1.53/0.59  fof(f961,plain,(
% 1.53/0.59    r2_hidden(sK5(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f949,f61])).
% 1.53/0.59  fof(f61,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f38,f36])).
% 1.53/0.59  fof(f38,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f18])).
% 1.53/0.59  fof(f18,plain,(
% 1.53/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.59    inference(ennf_transformation,[],[f15])).
% 1.53/0.59  fof(f15,plain,(
% 1.53/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.59    inference(rectify,[],[f4])).
% 1.53/0.59  fof(f4,axiom,(
% 1.53/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.53/0.59  fof(f949,plain,(
% 1.53/0.59    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.53/0.59    inference(trivial_inequality_removal,[],[f948])).
% 1.53/0.59  fof(f948,plain,(
% 1.53/0.59    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.53/0.59    inference(duplicate_literal_removal,[],[f941])).
% 1.53/0.59  fof(f941,plain,(
% 1.53/0.59    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.53/0.59    inference(superposition,[],[f25,f936])).
% 1.53/0.59  fof(f936,plain,(
% 1.53/0.59    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.53/0.59    inference(forward_demodulation,[],[f933,f463])).
% 1.53/0.59  fof(f463,plain,(
% 1.53/0.59    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.53/0.59    inference(backward_demodulation,[],[f411,f454])).
% 1.53/0.59  fof(f454,plain,(
% 1.53/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.53/0.59    inference(backward_demodulation,[],[f393,f453])).
% 1.53/0.59  fof(f453,plain,(
% 1.53/0.59    k1_xboole_0 = k2_relat_1(k2_relat_1(k1_xboole_0))),
% 1.53/0.59    inference(forward_demodulation,[],[f352,f421])).
% 1.53/0.59  fof(f421,plain,(
% 1.53/0.59    k2_relat_1(k1_xboole_0) = k10_relat_1(sK1,k1_xboole_0)),
% 1.53/0.59    inference(forward_demodulation,[],[f355,f358])).
% 1.53/0.59  fof(f358,plain,(
% 1.53/0.59    k2_relat_1(k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f110,f189,f41])).
% 1.53/0.59  fof(f41,plain,(
% 1.53/0.59    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0) | X0 = X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f21])).
% 1.53/0.59  fof(f21,plain,(
% 1.53/0.59    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.53/0.59    inference(ennf_transformation,[],[f3])).
% 1.53/0.59  fof(f3,axiom,(
% 1.53/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.53/0.59  fof(f189,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f184,f71])).
% 1.53/0.59  fof(f71,plain,(
% 1.53/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP8(X2,X0)) )),
% 1.53/0.59    inference(equality_resolution,[],[f46])).
% 1.53/0.59  fof(f46,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (sP8(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f10])).
% 1.53/0.59  fof(f184,plain,(
% 1.53/0.59    ( ! [X0] : (~sP8(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f176,f43])).
% 1.53/0.59  fof(f176,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f26,f90,f69])).
% 1.53/0.59  fof(f69,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.53/0.59    inference(equality_resolution,[],[f33])).
% 1.53/0.59  fof(f33,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.53/0.59    inference(cnf_transformation,[],[f17])).
% 1.53/0.59  fof(f90,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~sP3(X0,k1_xboole_0,X1)) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f82,f31])).
% 1.53/0.59  fof(f31,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X1) | ~sP3(X3,X1,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f17])).
% 1.53/0.59  fof(f82,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f27,f64])).
% 1.53/0.59  fof(f64,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f49,f28])).
% 1.53/0.59  fof(f28,plain,(
% 1.53/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f6])).
% 1.53/0.59  fof(f6,axiom,(
% 1.53/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.59  fof(f49,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f22])).
% 1.53/0.59  fof(f22,plain,(
% 1.53/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.59    inference(ennf_transformation,[],[f7])).
% 1.53/0.59  fof(f7,axiom,(
% 1.53/0.59    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.53/0.59  fof(f27,plain,(
% 1.53/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f5])).
% 1.53/0.59  fof(f5,axiom,(
% 1.53/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.53/0.59  fof(f26,plain,(
% 1.53/0.59    v1_relat_1(sK1)),
% 1.53/0.59    inference(cnf_transformation,[],[f16])).
% 1.53/0.59  fof(f16,plain,(
% 1.53/0.59    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.53/0.59    inference(ennf_transformation,[],[f14])).
% 1.53/0.59  fof(f14,negated_conjecture,(
% 1.53/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.53/0.59    inference(negated_conjecture,[],[f13])).
% 1.53/0.59  fof(f13,conjecture,(
% 1.53/0.59    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.53/0.59  fof(f110,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f100,f71])).
% 1.53/0.59  fof(f100,plain,(
% 1.53/0.59    ( ! [X0] : (~sP8(X0,k1_xboole_0)) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f82,f43])).
% 1.53/0.59  fof(f355,plain,(
% 1.53/0.59    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f176,f189,f41])).
% 1.53/0.59  fof(f352,plain,(
% 1.53/0.59    k1_xboole_0 = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f82,f189,f41])).
% 1.53/0.59  fof(f393,plain,(
% 1.53/0.59    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k1_xboole_0))),
% 1.53/0.59    inference(backward_demodulation,[],[f359,f358])).
% 1.53/0.59  fof(f359,plain,(
% 1.53/0.59    k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f120,f189,f41])).
% 1.53/0.59  fof(f120,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k2_relat_1(k1_xboole_0)))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f115,f71])).
% 1.53/0.59  fof(f115,plain,(
% 1.53/0.59    ( ! [X0] : (~sP8(X0,k2_relat_1(k1_xboole_0))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f110,f43])).
% 1.53/0.59  fof(f411,plain,(
% 1.53/0.59    k2_relat_1(k1_xboole_0) = k10_relat_1(sK1,k2_relat_1(k1_xboole_0))),
% 1.53/0.59    inference(forward_demodulation,[],[f356,f358])).
% 1.53/0.59  fof(f356,plain,(
% 1.53/0.59    k10_relat_1(sK1,k2_relat_1(k1_xboole_0)) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f177,f189,f41])).
% 1.53/0.59  fof(f177,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(k1_xboole_0)))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f26,f114,f69])).
% 1.53/0.59  fof(f114,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~sP3(X0,k2_relat_1(k1_xboole_0),X1)) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f110,f31])).
% 1.53/0.59  fof(f933,plain,(
% 1.53/0.59    ( ! [X0] : (k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.53/0.59    inference(superposition,[],[f669,f721])).
% 1.53/0.59  fof(f721,plain,(
% 1.53/0.59    ( ! [X2,X3] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3)) | ~r1_xboole_0(X2,X3)) )),
% 1.53/0.59    inference(resolution,[],[f717,f62])).
% 1.53/0.59  fof(f62,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f37,f36])).
% 1.53/0.59  fof(f37,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f18])).
% 1.53/0.59  fof(f717,plain,(
% 1.53/0.59    ( ! [X0] : (r2_hidden(sK7(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 1.53/0.59    inference(forward_demodulation,[],[f714,f454])).
% 1.53/0.59  fof(f714,plain,(
% 1.53/0.59    ( ! [X0] : (r2_hidden(sK7(k1_xboole_0,X0),X0) | k2_relat_1(k1_xboole_0) = X0) )),
% 1.53/0.59    inference(resolution,[],[f47,f100])).
% 1.53/0.59  fof(f47,plain,(
% 1.53/0.59    ( ! [X0,X1] : (sP8(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.53/0.59    inference(cnf_transformation,[],[f10])).
% 1.53/0.59  fof(f669,plain,(
% 1.53/0.59    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f26,f63])).
% 1.53/0.59  fof(f63,plain,(
% 1.53/0.59    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.53/0.59    inference(definition_unfolding,[],[f39,f36])).
% 1.53/0.59  fof(f39,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f19])).
% 1.53/0.59  fof(f19,plain,(
% 1.53/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.59    inference(ennf_transformation,[],[f12])).
% 1.53/0.59  fof(f12,axiom,(
% 1.53/0.59    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.53/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.53/0.59  fof(f25,plain,(
% 1.53/0.59    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.53/0.59    inference(cnf_transformation,[],[f16])).
% 1.53/0.59  fof(f959,plain,(
% 1.53/0.59    ( ! [X0] : (~sP3(X0,sK0,sK1)) )),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f949,f198])).
% 1.53/0.59  fof(f198,plain,(
% 1.53/0.59    ( ! [X0] : (~sP3(X0,sK0,sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.53/0.59    inference(global_subsumption,[],[f26,f82,f196])).
% 1.53/0.59  fof(f196,plain,(
% 1.53/0.59    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP3(X0,sK0,sK1) | ~v1_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.53/0.59    inference(superposition,[],[f70,f24])).
% 1.53/0.59  fof(f24,plain,(
% 1.53/0.59    k1_xboole_0 = k10_relat_1(sK1,sK0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.53/0.59    inference(cnf_transformation,[],[f16])).
% 1.53/0.59  fof(f70,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,k10_relat_1(X0,X1)) | ~sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.53/0.59    inference(equality_resolution,[],[f32])).
% 1.53/0.59  fof(f32,plain,(
% 1.53/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.53/0.59    inference(cnf_transformation,[],[f17])).
% 1.53/0.59  fof(f1011,plain,(
% 1.53/0.59    sP8(sK5(k2_relat_1(sK1),sK0),sK1)),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f998,f71])).
% 1.53/0.59  fof(f998,plain,(
% 1.53/0.59    r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.53/0.59    inference(unit_resulting_resolution,[],[f973,f55])).
% 1.53/0.59  fof(f55,plain,(
% 1.53/0.59    ( ! [X0,X3,X1] : (~sP12(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f1])).
% 1.53/0.59  % SZS output end Proof for theBenchmark
% 1.53/0.59  % (20581)------------------------------
% 1.53/0.59  % (20581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (20581)Termination reason: Refutation
% 1.53/0.59  
% 1.53/0.59  % (20581)Memory used [KB]: 6780
% 1.53/0.59  % (20581)Time elapsed: 0.174 s
% 1.53/0.59  % (20581)------------------------------
% 1.53/0.59  % (20581)------------------------------
% 1.53/0.60  % (20556)Success in time 0.236 s
%------------------------------------------------------------------------------
