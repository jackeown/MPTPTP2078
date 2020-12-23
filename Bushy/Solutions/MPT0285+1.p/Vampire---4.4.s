%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t92_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:13 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  82 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f43,f50,f57,f67,f70])).

fof(f70,plain,
    ( ~ spl2_2
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f68,f42])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f68,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f26,f56])).

fof(f56,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_7
  <=> ~ r1_tarski(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t92_zfmisc_1.p',l49_zfmisc_1)).

fof(f67,plain,
    ( ~ spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f60,f41,f65])).

fof(f65,plain,
    ( spl2_9
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f25,f42])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t92_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f57,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ~ r1_tarski(sK0,k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(X1))
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(sK0,k3_tarski(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t92_zfmisc_1.p',t92_zfmisc_1)).

fof(f50,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f48,plain,
    ( spl2_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f23,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t92_zfmisc_1.p',d2_xboole_0)).

fof(f43,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f34,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t92_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
