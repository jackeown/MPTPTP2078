%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t107_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:57 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 147 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 328 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f47,f55,f62,f71,f78,f87,f96,f103,f111,f123,f130,f140,f153,f160,f166])).

fof(f166,plain,
    ( spl4_7
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f163,f61])).

fof(f61,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_7
  <=> ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f163,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(resolution,[],[f116,f86])).

fof(f86,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_12
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f116,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,X5)
        | r2_hidden(k4_tarski(sK1,X4),k2_zfmisc_1(sK3,X5)) )
    | ~ spl4_18 ),
    inference(resolution,[],[f32,f110])).

fof(f110,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_18
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',l54_zfmisc_1)).

fof(f160,plain,
    ( ~ spl4_29
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f145,f138,f158])).

fof(f158,plain,
    ( spl4_29
  <=> ~ r2_hidden(k2_zfmisc_1(sK2,sK2),k4_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f138,plain,
    ( spl4_24
  <=> r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f145,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK2),k4_tarski(sK0,sK0))
    | ~ spl4_24 ),
    inference(resolution,[],[f139,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f139,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK2,sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f138])).

fof(f153,plain,
    ( ~ spl4_27
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f146,f138,f151])).

fof(f151,plain,
    ( spl4_27
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f146,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK2))
    | ~ spl4_24 ),
    inference(resolution,[],[f139,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',t7_boole)).

fof(f140,plain,
    ( spl4_24
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f132,f85,f138])).

fof(f132,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK2,sK2))
    | ~ spl4_12 ),
    inference(resolution,[],[f115,f86])).

fof(f115,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(sK2,X3)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f32,f86])).

fof(f130,plain,
    ( ~ spl4_23
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f112,f109,f128])).

fof(f128,plain,
    ( spl4_23
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f112,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl4_18 ),
    inference(resolution,[],[f110,f27])).

fof(f123,plain,
    ( ~ spl4_21
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f113,f109,f121])).

fof(f121,plain,
    ( spl4_21
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl4_18 ),
    inference(resolution,[],[f110,f29])).

fof(f111,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f104,f53,f109])).

fof(f53,plain,
    ( spl4_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,
    ( ~ spl4_17
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f88,f85,f101])).

fof(f101,plain,
    ( spl4_17
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f88,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f86,f27])).

fof(f96,plain,
    ( ~ spl4_15
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f89,f85,f94])).

fof(f94,plain,
    ( spl4_15
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f89,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl4_12 ),
    inference(resolution,[],[f86,f29])).

fof(f87,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f80,f53,f85])).

fof(f80,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f30,f54])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,
    ( ~ spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f63,f53,f76])).

fof(f76,plain,
    ( spl4_11
  <=> ~ r2_hidden(k2_zfmisc_1(sK2,sK3),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f63,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),k4_tarski(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f54,f27])).

fof(f71,plain,
    ( ~ spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f64,f53,f69])).

fof(f69,plain,
    ( spl4_9
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f64,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f54,f29])).

fof(f62,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
        & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
       => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',t107_zfmisc_1)).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f45,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f25,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',d2_xboole_0)).

fof(f40,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f33,f38])).

fof(f38,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f24,f25])).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
