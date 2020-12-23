%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t73_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 156 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  210 ( 440 expanded)
%              Number of equality atoms :   37 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f60,f75,f84,f91,f98,f106,f123,f133,f148,f158,f163,f165,f171])).

fof(f171,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f166,f68])).

fof(f68,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_4
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f166,plain,
    ( ! [X0] : k4_xboole_0(k2_tarski(sK0,X0),sK2) != k1_xboole_0
    | ~ spl3_7 ),
    inference(resolution,[],[f71,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k2_tarski(X0,X2),X1) != k1_xboole_0 ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',t37_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',t38_zfmisc_1)).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_7
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f165,plain,
    ( spl3_7
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f71,f150])).

fof(f150,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f147,f43])).

fof(f147,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_16
  <=> r1_tarski(k2_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f163,plain,
    ( spl3_5
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f65,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_5
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f161,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0
    | ~ spl3_18 ),
    inference(resolution,[],[f157,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f157,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_18
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f158,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f141,f96,f73,f156])).

fof(f73,plain,
    ( spl3_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,
    ( spl3_12
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f141,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(resolution,[],[f111,f97])).

fof(f97,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r1_tarski(k2_tarski(sK0,X0),sK2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f74])).

fof(f74,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f148,plain,
    ( spl3_16
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f139,f73,f146])).

fof(f139,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f111,f74])).

fof(f133,plain,
    ( ~ spl3_15
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f125,f96,f131])).

fof(f131,plain,
    ( spl3_15
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f125,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl3_12 ),
    inference(resolution,[],[f97,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f123,plain,
    ( ~ spl3_4
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(superposition,[],[f115,f68])).

fof(f115,plain,
    ( ! [X0] : k4_xboole_0(k2_tarski(X0,sK1),sK2) != k1_xboole_0
    | ~ spl3_13 ),
    inference(superposition,[],[f110,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',commutativity_k2_tarski)).

fof(f110,plain,
    ( ! [X7] : k4_xboole_0(k2_tarski(sK1,X7),sK2) != k1_xboole_0
    | ~ spl3_13 ),
    inference(resolution,[],[f100,f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_13
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f106,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f31,f93,f70,f64])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',t73_zfmisc_1)).

fof(f98,plain,
    ( spl3_4
    | spl3_12 ),
    inference(avatar_split_clause,[],[f30,f96,f67])).

fof(f30,plain,
    ( r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,
    ( ~ spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f76,f73,f89])).

fof(f89,plain,
    ( spl3_11
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f76,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f74,f38])).

fof(f84,plain,
    ( ~ spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f77,f73,f82])).

fof(f82,plain,
    ( spl3_9
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',t7_boole)).

fof(f75,plain,
    ( spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f29,f73,f67])).

fof(f29,plain,
    ( r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f58,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',d2_xboole_0)).

fof(f53,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f46,f51])).

fof(f51,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f32,f33])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t73_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
