%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t66_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:30 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 118 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f62,f104,f107])).

fof(f107,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f58,f93])).

fof(f93,plain,(
    ! [X8] : r1_xboole_0(k1_xboole_0,X8) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,(
    ! [X8] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X8) ) ),
    inference(superposition,[],[f45,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t66_xboole_1.p',t2_boole)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t66_xboole_1.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t66_xboole_1.p',d7_xboole_0)).

fof(f58,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_5
  <=> ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f104,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f99,f61])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f99,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_2
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f44,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t66_xboole_1.p',idempotence_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,
    ( ~ spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f55,f60,f57])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( r1_xboole_0(sK0,sK0)
      & k1_xboole_0 != sK0 )
    | ( k1_xboole_0 = sK0
      & ~ r1_xboole_0(sK0,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) )
   => ( ( r1_xboole_0(sK0,sK0)
        & k1_xboole_0 != sK0 )
      | ( k1_xboole_0 = sK0
        & ~ r1_xboole_0(sK0,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t66_xboole_1.p',t66_xboole_1)).

fof(f54,plain,
    ( spl2_0
    | spl2_2 ),
    inference(avatar_split_clause,[],[f33,f52,f49])).

fof(f49,plain,
    ( spl2_0
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
