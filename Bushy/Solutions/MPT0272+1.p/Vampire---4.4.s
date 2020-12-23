%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t69_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 (  82 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f53,f60,f68,f83])).

fof(f83,plain,
    ( spl2_5
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f81,f59])).

fof(f59,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_5
  <=> k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f81,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0
    | ~ spl2_7 ),
    inference(superposition,[],[f67,f72])).

fof(f72,plain,(
    ! [X2,X3] :
      ( k1_tarski(X2) = k4_xboole_0(k1_tarski(X2),X3)
      | k4_xboole_0(k1_tarski(X2),X3) = k1_xboole_0 ) ),
    inference(resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t69_zfmisc_1.p',l35_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t69_zfmisc_1.p',l33_zfmisc_1)).

fof(f67,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_7
  <=> k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f68,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t69_zfmisc_1.p',t69_zfmisc_1)).

fof(f60,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f51,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f28,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t69_zfmisc_1.p',d2_xboole_0)).

fof(f46,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f39,f44])).

fof(f44,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f27,f28])).

fof(f27,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t69_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
