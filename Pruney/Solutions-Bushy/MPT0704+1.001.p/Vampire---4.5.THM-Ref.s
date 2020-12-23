%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0704+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:30 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 291 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  397 ( 920 expanded)
%              Number of equality atoms :   73 ( 118 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f123,f221,f230,f387,f750,f757,f760,f809])).

fof(f809,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | ~ spl10_5 ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,
    ( ! [X0] : k1_tarski(X0) != k1_tarski(sK2(sK3(sK0)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_5
  <=> ! [X0] : k1_tarski(X0) != k1_tarski(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f760,plain,
    ( ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f758,f92])).

fof(f92,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(backward_demodulation,[],[f33,f87])).

fof(f87,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f758,plain,
    ( ! [X2] : ~ r1_tarski(o_0_0_xboole_0,k1_tarski(X2))
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f80,f238])).

fof(f238,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl10_8
  <=> o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f80,plain,
    ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl10_2
  <=> ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f757,plain,(
    ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl10_14 ),
    inference(resolution,[],[f749,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f749,plain,
    ( ! [X15] : ~ r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X15))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f748])).

fof(f748,plain,
    ( spl10_14
  <=> ! [X15] : ~ r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f750,plain,
    ( spl10_8
    | spl10_14
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f733,f79,f75,f748,f236])).

fof(f75,plain,
    ( spl10_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f733,plain,
    ( ! [X15] :
        ( ~ r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X15))
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(superposition,[],[f80,f712])).

fof(f712,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0))
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl10_1 ),
    inference(resolution,[],[f711,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK0))
      | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f101,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
      | o_0_0_xboole_0 = k10_relat_1(sK0,X0) ) ),
    inference(resolution,[],[f89,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
        <=> ! [X1] :
            ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | o_0_0_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(backward_demodulation,[],[f50,f87])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f711,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f710,f30])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f709,f31])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f709,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) )
    | ~ spl10_1 ),
    inference(resolution,[],[f37,f76])).

fof(f76,plain,
    ( v2_funct_1(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(f387,plain,
    ( ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f385,f71])).

fof(f71,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f385,plain,
    ( ~ r2_hidden(sK3(sK0),k1_tarski(sK3(sK0)))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f374,f93])).

fof(f93,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(resolution,[],[f61,f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f374,plain,
    ( r2_hidden(sK6(sK0,sK3(sK0)),o_0_0_xboole_0)
    | ~ r2_hidden(sK3(sK0),k1_tarski(sK3(sK0)))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(superposition,[],[f350,f119])).

fof(f119,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl10_4
  <=> o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f350,plain,
    ( ! [X4] :
        ( r2_hidden(sK6(sK0,sK3(sK0)),k10_relat_1(sK0,X4))
        | ~ r2_hidden(sK3(sK0),X4) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f345,f255])).

fof(f255,plain,
    ( sK3(sK0) = k1_funct_1(sK0,sK6(sK0,sK3(sK0)))
    | ~ spl10_7 ),
    inference(resolution,[],[f220,f198])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK0,sK6(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f197,f30])).

fof(f197,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | k1_funct_1(sK0,sK6(sK0,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f64,f31])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK6(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f220,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl10_7
  <=> r2_hidden(sK3(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f345,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK6(sK0,sK3(sK0))),X4)
        | r2_hidden(sK6(sK0,sK3(sK0)),k10_relat_1(sK0,X4)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f342,f215])).

fof(f215,plain,
    ( r2_hidden(sK6(sK0,sK3(sK0)),k1_relat_1(sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl10_6
  <=> r2_hidden(sK6(sK0,sK3(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f342,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(k1_funct_1(sK0,X0),X1)
      | r2_hidden(X0,k10_relat_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f341,f30])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(k1_funct_1(sK0,X0),X1)
      | r2_hidden(X0,k10_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f66,f31])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f230,plain,
    ( spl10_1
    | spl10_6 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl10_1
    | spl10_6 ),
    inference(subsumption_resolution,[],[f228,f30])).

fof(f228,plain,
    ( ~ v1_relat_1(sK0)
    | spl10_1
    | spl10_6 ),
    inference(subsumption_resolution,[],[f227,f77])).

fof(f77,plain,
    ( ~ v2_funct_1(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f227,plain,
    ( v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl10_6 ),
    inference(subsumption_resolution,[],[f225,f31])).

fof(f225,plain,
    ( ~ v1_funct_1(sK0)
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl10_6 ),
    inference(resolution,[],[f224,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f224,plain,
    ( ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | spl10_6 ),
    inference(subsumption_resolution,[],[f223,f30])).

fof(f223,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | spl10_6 ),
    inference(subsumption_resolution,[],[f222,f31])).

fof(f222,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | spl10_6 ),
    inference(resolution,[],[f216,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK6(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f216,plain,
    ( ~ r2_hidden(sK6(sK0,sK3(sK0)),k1_relat_1(sK0))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f221,plain,
    ( ~ spl10_6
    | spl10_7
    | spl10_1 ),
    inference(avatar_split_clause,[],[f212,f75,f218,f214])).

fof(f212,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ r2_hidden(sK6(sK0,sK3(sK0)),k1_relat_1(sK0))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f211,f30])).

fof(f211,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ r2_hidden(sK6(sK0,sK3(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f210,f31])).

fof(f210,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ r2_hidden(sK6(sK0,sK3(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl10_1 ),
    inference(superposition,[],[f63,f208])).

fof(f208,plain,
    ( sK3(sK0) = k1_funct_1(sK0,sK6(sK0,sK3(sK0)))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f207,f30])).

fof(f207,plain,
    ( sK3(sK0) = k1_funct_1(sK0,sK6(sK0,sK3(sK0)))
    | ~ v1_relat_1(sK0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f206,f77])).

fof(f206,plain,
    ( sK3(sK0) = k1_funct_1(sK0,sK6(sK0,sK3(sK0)))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f202,f31])).

fof(f202,plain,
    ( sK3(sK0) = k1_funct_1(sK0,sK6(sK0,sK3(sK0)))
    | ~ v1_funct_1(sK0)
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f198,f35])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f123,plain,
    ( spl10_4
    | spl10_5
    | spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f115,f83,f75,f121,f117])).

fof(f83,plain,
    ( spl10_3
  <=> ! [X1] : r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f115,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK2(sK3(sK0)))
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | spl10_1
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f114,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK2(sK3(sK0)))
        | ~ v1_relat_1(sK0)
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | spl10_1
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f113,f77])).

fof(f113,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK2(sK3(sK0)))
        | v2_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f112,f31])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK2(sK3(sK0)))
        | ~ v1_funct_1(sK0)
        | v2_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | ~ spl10_3 ),
    inference(superposition,[],[f36,f100])).

fof(f100,plain,
    ( ! [X2] :
        ( k1_tarski(sK2(X2)) = k10_relat_1(sK0,k1_tarski(X2))
        | o_0_0_xboole_0 = k10_relat_1(sK0,k1_tarski(X2)) )
    | ~ spl10_3 ),
    inference(resolution,[],[f88,f84])).

fof(f84,plain,
    ( ! [X1] : r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f58,f87])).

% (31393)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0] :
      ( k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK3(X0)))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f28,f83,f75])).

fof(f28,plain,(
    ! [X1] :
      ( r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1)))
      | v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f29,f79,f75])).

fof(f29,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
