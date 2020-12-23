%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t51_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  35 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f52,f59,f67,f81])).

fof(f81,plain,
    ( spl2_3
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f77,f66])).

fof(f66,plain,
    ( k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_6
  <=> k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f77,plain,
    ( k1_tarski(sK1) != k3_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_3
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t51_zfmisc_1.p',l29_zfmisc_1)).

fof(f67,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK1,sK0)
    & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK1,sK0)
      & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t51_zfmisc_1.p',t51_zfmisc_1)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f57,plain,
    ( spl2_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f28,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t51_zfmisc_1.p',d2_xboole_0)).

fof(f52,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f27,f43])).

fof(f43,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f27,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t51_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
