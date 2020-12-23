%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0485+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  54 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 121 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f912,f916,f1027,f1111,f1306])).

fof(f1306,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_18 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f915,f1110,f911,f859])).

fof(f859,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f760])).

fof(f760,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f759])).

fof(f759,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f723,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f911,plain,
    ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f910])).

fof(f910,plain,
    ( spl13_1
  <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1110,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1109,plain,
    ( spl13_18
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f915,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl13_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1111,plain,
    ( spl13_18
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(avatar_split_clause,[],[f1107,f1025,f914,f1109])).

fof(f1025,plain,
    ( spl13_11
  <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f1107,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f1106,f866])).

fof(f866,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f1106,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f1103,f915])).

fof(f1103,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl13_11 ),
    inference(superposition,[],[f841,f1026])).

fof(f1026,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f841,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f750])).

fof(f750,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1027,plain,
    ( spl13_11
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f1022,f914,f1025])).

fof(f1022,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl13_2 ),
    inference(resolution,[],[f862,f915])).

fof(f862,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f762])).

fof(f762,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f722])).

fof(f722,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f916,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f819,f914])).

fof(f819,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f790])).

fof(f790,plain,
    ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f728,f789])).

fof(f789,plain,
    ( ? [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f728,plain,(
    ? [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f725])).

fof(f725,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f724])).

fof(f724,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f912,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f820,f910])).

fof(f820,plain,(
    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f790])).
%------------------------------------------------------------------------------
