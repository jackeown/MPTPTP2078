%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0275+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 118 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  192 ( 383 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f34,f35,f39,f43,f47,f51,f55,f61,f72,f78,f79,f80,f91])).

fof(f91,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f84,f70])).

fof(f70,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_11
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f84,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r1_tarski(k2_tarski(sK0,X0),sK2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r1_tarski(k2_tarski(sK0,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f75,f69,f37,f22])).

fof(f22,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f71,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f79,plain,
    ( spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f74,f69,f49,f30])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f71,f50])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( spl3_2
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f73,f69,f53,f26])).

fof(f26,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f73,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f72,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f67,f41,f22,f69])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f67,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f42,f23])).

fof(f23,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f61,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f56,f45,f26,f59])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r1_tarski(k2_tarski(sK0,X0),sK2) )
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f46,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_tarski(X0,X1),X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f55,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f18,f53])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f51,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f13,f26,f22])).

fof(f13,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f34,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f14,f30,f22])).

fof(f14,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f30,f26,f22])).

fof(f15,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
