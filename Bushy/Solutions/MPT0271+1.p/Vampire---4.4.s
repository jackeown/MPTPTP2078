%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t68_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:10 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (  71 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 159 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f50,f64,f73,f80,f81,f86,f90])).

fof(f90,plain,
    ( ~ spl2_4
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f88,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_7
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f88,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f32,f57])).

fof(f57,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_4
  <=> k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t68_zfmisc_1.p',l35_zfmisc_1)).

fof(f86,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f84,f54])).

fof(f54,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_5
  <=> k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f84,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0
    | ~ spl2_6 ),
    inference(resolution,[],[f33,f63])).

fof(f63,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,
    ( ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f25,f59,f53])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 )
    & ( r2_hidden(sK0,sK1)
      | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 )
      & ( r2_hidden(sK0,sK1)
        | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t68_zfmisc_1.p',t68_zfmisc_1)).

fof(f80,plain,
    ( ~ spl2_11
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f65,f62,f78])).

fof(f78,plain,
    ( spl2_11
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f65,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t68_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f73,plain,
    ( ~ spl2_9
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f66,f62,f71])).

fof(f71,plain,
    ( spl2_9
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f66,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t68_zfmisc_1.p',t7_boole)).

fof(f64,plain,
    ( spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f24,f62,f56])).

fof(f24,plain,
    ( r2_hidden(sK0,sK1)
    | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f48,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f27,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t68_zfmisc_1.p',d2_xboole_0)).

fof(f43,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f36,f41])).

fof(f41,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f26,f27])).

fof(f26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t68_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
