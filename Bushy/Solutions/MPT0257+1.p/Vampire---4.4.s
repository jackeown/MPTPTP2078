%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t52_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  82 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f52,f59,f68,f76,f88])).

fof(f88,plain,
    ( ~ spl2_2
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f86,f67])).

fof(f67,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_7
  <=> k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f86,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t52_zfmisc_1.p',l31_zfmisc_1)).

fof(f76,plain,
    ( ~ spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f69,f50,f74])).

fof(f74,plain,
    ( spl2_9
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f69,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f33,f51])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t52_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f68,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t52_zfmisc_1.p',t52_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t52_zfmisc_1.p',d2_xboole_0)).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t52_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
