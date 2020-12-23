%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 153 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  239 ( 348 expanded)
%              Number of equality atoms :   80 ( 124 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f600,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f70,f74,f82,f86,f98,f102,f125,f138,f189,f233,f262,f309,f380,f570,f576,f598])).

fof(f598,plain,
    ( ~ spl2_18
    | spl2_41
    | spl2_45 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | ~ spl2_18
    | spl2_41
    | spl2_45 ),
    inference(subsumption_resolution,[],[f313,f378])).

fof(f378,plain,
    ( sK0 != sK1
    | spl2_45 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl2_45
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f313,plain,
    ( sK0 = sK1
    | ~ spl2_18
    | spl2_41 ),
    inference(unit_resulting_resolution,[],[f308,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f308,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_41 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl2_41
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f576,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_27
    | ~ spl2_45
    | ~ spl2_64 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_27
    | ~ spl2_45
    | ~ spl2_64 ),
    inference(subsumption_resolution,[],[f455,f571])).

fof(f571,plain,
    ( ! [X1] : k1_tarski(X1) = k3_tarski(k1_tarski(k1_tarski(X1)))
    | ~ spl2_27
    | ~ spl2_64 ),
    inference(superposition,[],[f569,f188])).

fof(f188,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl2_27
  <=> ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f569,plain,
    ( ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl2_64
  <=> ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f455,plain,
    ( k1_tarski(sK0) != k3_tarski(k1_tarski(k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f454,f56])).

fof(f56,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_3
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f454,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f444,f56])).

fof(f444,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_45 ),
    inference(superposition,[],[f48,f379])).

fof(f379,plain,
    ( sK0 = sK1
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f377])).

fof(f48,plain,
    ( k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f570,plain,
    ( spl2_64
    | ~ spl2_7
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f235,f231,f72,f568])).

fof(f72,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f231,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( k2_xboole_0(X1,X0) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f235,plain,
    ( ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))
    | ~ spl2_7
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f73,f232])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f231])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f380,plain,
    ( spl2_45
    | ~ spl2_9
    | spl2_40 ),
    inference(avatar_split_clause,[],[f310,f302,f80,f377])).

fof(f80,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f302,plain,
    ( spl2_40
  <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f310,plain,
    ( sK0 = sK1
    | ~ spl2_9
    | spl2_40 ),
    inference(unit_resulting_resolution,[],[f304,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f304,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl2_40 ),
    inference(avatar_component_clause,[],[f302])).

fof(f309,plain,
    ( ~ spl2_40
    | ~ spl2_41
    | spl2_16
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f272,f260,f122,f306,f302])).

fof(f122,plain,
    ( spl2_16
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f260,plain,
    ( spl2_36
  <=> ! [X3,X2] :
        ( k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2)
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f272,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl2_16
    | ~ spl2_36 ),
    inference(superposition,[],[f124,f261])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f260])).

fof(f124,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f262,plain,
    ( spl2_36
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f131,f100,f84,f260])).

fof(f84,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f100,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f131,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(superposition,[],[f101,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f101,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f233,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f132,f100,f96,f51,f231])).

fof(f51,plain,
    ( spl2_2
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f96,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_2
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f130,f52])).

fof(f52,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f101,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f189,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f107,f68,f55,f187])).

fof(f68,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f107,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f69,f56])).

fof(f69,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f138,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f36,f136])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f125,plain,
    ( ~ spl2_16
    | spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f108,f68,f46,f122])).

fof(f108,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f48,f69])).

fof(f102,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f33,f100])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f98,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f86,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f82,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f74,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f66,f59,f55,f72])).

fof(f59,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f60,f56])).

fof(f60,plain,
    ( ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f70,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f61,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f57,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f49,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (22591)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (22577)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (22583)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (22593)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (22594)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (22584)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (22585)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (22583)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (22580)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (22578)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f600,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f70,f74,f82,f86,f98,f102,f125,f138,f189,f233,f262,f309,f380,f570,f576,f598])).
% 0.21/0.47  fof(f598,plain,(
% 0.21/0.47    ~spl2_18 | spl2_41 | spl2_45),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f597])).
% 0.21/0.47  fof(f597,plain,(
% 0.21/0.47    $false | (~spl2_18 | spl2_41 | spl2_45)),
% 0.21/0.47    inference(subsumption_resolution,[],[f313,f378])).
% 0.21/0.47  fof(f378,plain,(
% 0.21/0.47    sK0 != sK1 | spl2_45),
% 0.21/0.47    inference(avatar_component_clause,[],[f377])).
% 0.21/0.47  fof(f377,plain,(
% 0.21/0.47    spl2_45 <=> sK0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.47  fof(f313,plain,(
% 0.21/0.47    sK0 = sK1 | (~spl2_18 | spl2_41)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f308,f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl2_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl2_18 <=> ! [X1,X0] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.47  fof(f308,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_41),
% 0.21/0.47    inference(avatar_component_clause,[],[f306])).
% 0.21/0.47  fof(f306,plain,(
% 0.21/0.47    spl2_41 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.47  fof(f576,plain,(
% 0.21/0.47    spl2_1 | ~spl2_3 | ~spl2_27 | ~spl2_45 | ~spl2_64),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f575])).
% 0.21/0.47  fof(f575,plain,(
% 0.21/0.47    $false | (spl2_1 | ~spl2_3 | ~spl2_27 | ~spl2_45 | ~spl2_64)),
% 0.21/0.47    inference(subsumption_resolution,[],[f455,f571])).
% 0.21/0.47  fof(f571,plain,(
% 0.21/0.47    ( ! [X1] : (k1_tarski(X1) = k3_tarski(k1_tarski(k1_tarski(X1)))) ) | (~spl2_27 | ~spl2_64)),
% 0.21/0.47    inference(superposition,[],[f569,f188])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) ) | ~spl2_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f187])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    spl2_27 <=> ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.47  fof(f569,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) ) | ~spl2_64),
% 0.21/0.47    inference(avatar_component_clause,[],[f568])).
% 0.21/0.47  fof(f568,plain,(
% 0.21/0.47    spl2_64 <=> ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 0.21/0.47  fof(f455,plain,(
% 0.21/0.47    k1_tarski(sK0) != k3_tarski(k1_tarski(k1_tarski(sK0))) | (spl2_1 | ~spl2_3 | ~spl2_45)),
% 0.21/0.47    inference(forward_demodulation,[],[f454,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl2_3 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f454,plain,(
% 0.21/0.47    k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0))) | (spl2_1 | ~spl2_3 | ~spl2_45)),
% 0.21/0.47    inference(forward_demodulation,[],[f444,f56])).
% 0.21/0.47  fof(f444,plain,(
% 0.21/0.47    k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0))) | (spl2_1 | ~spl2_45)),
% 0.21/0.47    inference(superposition,[],[f48,f379])).
% 0.21/0.47  fof(f379,plain,(
% 0.21/0.47    sK0 = sK1 | ~spl2_45),
% 0.21/0.47    inference(avatar_component_clause,[],[f377])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl2_1 <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f570,plain,(
% 0.21/0.47    spl2_64 | ~spl2_7 | ~spl2_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f235,f231,f72,f568])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl2_7 <=> ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    spl2_32 <=> ! [X1,X0] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) ) | (~spl2_7 | ~spl2_32)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f73,f232])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1)) ) | ~spl2_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f231])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_tarski(X0))) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f380,plain,(
% 0.21/0.47    spl2_45 | ~spl2_9 | spl2_40),
% 0.21/0.47    inference(avatar_split_clause,[],[f310,f302,f80,f377])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl2_9 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f302,plain,(
% 0.21/0.47    spl2_40 <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    sK0 = sK1 | (~spl2_9 | spl2_40)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f304,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f80])).
% 0.21/0.47  fof(f304,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl2_40),
% 0.21/0.47    inference(avatar_component_clause,[],[f302])).
% 0.21/0.47  fof(f309,plain,(
% 0.21/0.47    ~spl2_40 | ~spl2_41 | spl2_16 | ~spl2_36),
% 0.21/0.47    inference(avatar_split_clause,[],[f272,f260,f122,f306,f302])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl2_16 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    spl2_36 <=> ! [X3,X2] : (k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | (spl2_16 | ~spl2_36)),
% 0.21/0.47    inference(superposition,[],[f124,f261])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) ) | ~spl2_36),
% 0.21/0.47    inference(avatar_component_clause,[],[f260])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f122])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    spl2_36 | ~spl2_10 | ~spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f131,f100,f84,f260])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl2_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl2_14 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) ) | (~spl2_10 | ~spl2_14)),
% 0.21/0.47    inference(superposition,[],[f101,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    spl2_32 | ~spl2_2 | ~spl2_13 | ~spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f132,f100,f96,f51,f231])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl2_2 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl2_13 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1)) ) | (~spl2_2 | ~spl2_13 | ~spl2_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f130,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) ) | (~spl2_13 | ~spl2_14)),
% 0.21/0.47    inference(superposition,[],[f101,f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    spl2_27 | ~spl2_3 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f68,f55,f187])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) ) | (~spl2_3 | ~spl2_6)),
% 0.21/0.47    inference(superposition,[],[f69,f56])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    spl2_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f136])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~spl2_16 | spl2_1 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f108,f68,f46,f122])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | (spl2_1 | ~spl2_6)),
% 0.21/0.47    inference(superposition,[],[f48,f69])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f100])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f96])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f84])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f80])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl2_7 | ~spl2_3 | ~spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f66,f59,f55,f72])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl2_4 <=> ! [X1,X0] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_tarski(X0))) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.47    inference(superposition,[],[f60,f56])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f68])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f46])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f17])).
% 0.21/0.47  fof(f17,conjecture,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22583)------------------------------
% 0.21/0.47  % (22583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22583)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22583)Memory used [KB]: 6396
% 0.21/0.47  % (22583)Time elapsed: 0.062 s
% 0.21/0.47  % (22583)------------------------------
% 0.21/0.47  % (22583)------------------------------
% 0.21/0.48  % (22574)Success in time 0.118 s
%------------------------------------------------------------------------------
