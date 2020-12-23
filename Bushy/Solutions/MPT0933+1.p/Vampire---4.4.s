%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t94_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  87 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 284 expanded)
%              Number of equality atoms :   35 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f63,f70,f77,f84,f91,f100,f112])).

fof(f112,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f110,f69])).

fof(f69,plain,
    ( sK0 != sK2
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_7
  <=> sK0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( sK0 = sK2
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f109,f108])).

fof(f108,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK2
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f107,f76])).

fof(f76,plain,
    ( k1_mcart_1(sK0) = k1_mcart_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_8
  <=> k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f107,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK0)) = sK2
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f106,f83])).

fof(f83,plain,
    ( k2_mcart_1(sK0) = k2_mcart_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_10
  <=> k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f48,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f104,plain,
    ( ~ v1_relat_1(sK1)
    | k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t94_mcart_1.p',t23_mcart_1)).

fof(f109,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0
    | ~ spl3_0
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f105,f48])).

fof(f105,plain,
    ( ~ v1_relat_1(sK1)
    | k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0
    | ~ spl3_4 ),
    inference(resolution,[],[f35,f62])).

fof(f62,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f100,plain,
    ( ~ spl3_15
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f92,f54,f98])).

fof(f98,plain,
    ( spl3_15
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f55])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t94_mcart_1.p',t7_boole)).

fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f89,plain,
    ( spl3_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f38,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t94_mcart_1.p',d2_xboole_0)).

fof(f84,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
              & k1_mcart_1(X0) = k1_mcart_1(X2)
              & r2_hidden(X0,X1)
              & r2_hidden(X2,X1) )
           => X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t94_mcart_1.p',t94_mcart_1)).

fof(f77,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f34,f47])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
