%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t40_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 123 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f53,f60,f67,f74,f81])).

fof(f81,plain,
    ( ~ spl3_2
    | spl3_5
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f78,f59])).

fof(f59,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_5
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f77,f73])).

fof(f73,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_9
  <=> ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(X0)))
        | r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X0)
      | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t40_zfmisc_1.p',l2_zfmisc_1)).

fof(f74,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    & ~ r2_hidden(sK2,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        & ~ r2_hidden(X2,X0)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
      & ~ r2_hidden(sK2,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
          | r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t40_zfmisc_1.p',t40_zfmisc_1)).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f65,plain,
    ( spl3_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f29,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t40_zfmisc_1.p',d2_xboole_0)).

fof(f60,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f44,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f28,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t40_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
