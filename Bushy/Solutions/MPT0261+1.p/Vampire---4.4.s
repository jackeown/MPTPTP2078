%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t56_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:09 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   28 (  35 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f46,f53,f60,f65])).

fof(f65,plain,
    ( spl2_3
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f62,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_3
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f62,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f27,f59])).

fof(f59,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_7
  <=> ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t56_zfmisc_1.p',l27_zfmisc_1)).

fof(f60,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t56_zfmisc_1.p',t56_zfmisc_1)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f51,plain,
    ( spl2_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f25,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t56_zfmisc_1.p',d2_xboole_0)).

fof(f46,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f37,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t56_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
