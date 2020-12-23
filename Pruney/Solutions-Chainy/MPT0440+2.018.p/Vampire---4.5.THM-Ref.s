%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 3.90s
% Output     : Refutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 372 expanded)
%              Number of leaves         :   28 ( 138 expanded)
%              Depth                    :   12
%              Number of atoms          :  392 (1058 expanded)
%              Number of equality atoms :  117 ( 382 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f146,f251,f567,f697,f2850,f3318,f3321,f3337,f3358,f3398])).

fof(f3398,plain,
    ( sK1 != sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3358,plain,
    ( spl9_2
    | ~ spl9_5
    | ~ spl9_15
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f3357])).

fof(f3357,plain,
    ( $false
    | spl9_2
    | ~ spl9_5
    | ~ spl9_15
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f3356,f78])).

fof(f78,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl9_2
  <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f3356,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl9_5
    | ~ spl9_15
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f3355,f125])).

fof(f125,plain,
    ( ! [X9] : r2_hidden(X9,k2_enumset1(X9,X9,X9,X9))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_5
  <=> ! [X9] : r2_hidden(X9,k2_enumset1(X9,X9,X9,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f3355,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl9_15
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f3352,f287])).

fof(f287,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl9_15
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f3352,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl9_106 ),
    inference(superposition,[],[f160,f3263])).

fof(f3263,plain,
    ( sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f3261])).

fof(f3261,plain,
    ( spl9_106
  <=> sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k2_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f39,f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3337,plain,
    ( spl9_111
    | spl9_2
    | ~ spl9_12
    | ~ spl9_104 ),
    inference(avatar_split_clause,[],[f3336,f3250,f233,f76,f3315])).

fof(f3315,plain,
    ( spl9_111
  <=> r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f233,plain,
    ( spl9_12
  <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f3250,plain,
    ( spl9_104
  <=> sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f3336,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | spl9_2
    | ~ spl9_12
    | ~ spl9_104 ),
    inference(subsumption_resolution,[],[f3335,f301])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
        | r2_hidden(k4_tarski(sK0,X0),sK2) )
    | ~ spl9_12 ),
    inference(superposition,[],[f70,f235])).

fof(f235,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f233])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f3335,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl9_2
    | ~ spl9_104 ),
    inference(subsumption_resolution,[],[f3334,f78])).

fof(f3334,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_104 ),
    inference(superposition,[],[f38,f3252])).

fof(f3252,plain,
    ( sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_104 ),
    inference(avatar_component_clause,[],[f3250])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3321,plain,
    ( spl9_106
    | spl9_2
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f3320,f233,f76,f3261])).

fof(f3320,plain,
    ( sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl9_2
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f3319,f306])).

fof(f306,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),sK2)
        | sK1 = X9 )
    | ~ spl9_12 ),
    inference(superposition,[],[f60,f235])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f3319,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl9_2
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f3300,f78])).

fof(f3300,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_12 ),
    inference(resolution,[],[f301,f1225])).

fof(f1225,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | sK1 = sK3(sK2,X0) )
    | ~ spl9_12 ),
    inference(superposition,[],[f196,f235])).

fof(f196,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11),X11)
      | k2_relat_1(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10))) = X11
      | sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11) = X10 ) ),
    inference(resolution,[],[f38,f60])).

fof(f3318,plain,
    ( spl9_104
    | spl9_111
    | spl9_2
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f3313,f233,f76,f3315,f3250])).

fof(f3313,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl9_2
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f3299,f78])).

fof(f3299,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_12 ),
    inference(resolution,[],[f301,f1258])).

fof(f1258,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | sK0 = sK4(sK2,X0) )
    | ~ spl9_12 ),
    inference(superposition,[],[f199,f235])).

fof(f199,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(sK3(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18),X18)
      | k2_relat_1(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17)) = X18
      | sK4(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18) = X16 ) ),
    inference(resolution,[],[f38,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2850,plain,
    ( spl9_1
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2849,f233,f72])).

fof(f72,plain,
    ( spl9_1
  <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2849,plain,
    ( k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f2795,f1163])).

fof(f1163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK2,X0),k2_enumset1(sK0,sK0,sK0,sK0))
        | k1_relat_1(sK2) = X0
        | ~ r2_hidden(sK6(sK2,X0),X0) )
    | ~ spl9_12 ),
    inference(superposition,[],[f165,f235])).

fof(f165,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK6(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)),X4),X4)
      | k1_relat_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) = X4
      | ~ r2_hidden(sK6(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)),X4),X2) ) ),
    inference(resolution,[],[f43,f69])).

fof(f69,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f2795,plain,
    ( r2_hidden(sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl9_12 ),
    inference(factoring,[],[f1332])).

fof(f1332,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK2,X0),k2_enumset1(sK0,sK0,sK0,sK0))
        | k1_relat_1(sK2) = X0
        | r2_hidden(sK6(sK2,X0),X0) )
    | ~ spl9_12 ),
    inference(superposition,[],[f209,f235])).

fof(f209,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK6(k2_zfmisc_1(X6,k2_enumset1(X7,X7,X7,X7)),X8),X8)
      | k1_relat_1(k2_zfmisc_1(X6,k2_enumset1(X7,X7,X7,X7))) = X8
      | r2_hidden(sK6(k2_zfmisc_1(X6,k2_enumset1(X7,X7,X7,X7)),X8),X6) ) ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f697,plain,
    ( spl9_15
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f276,f270,f285])).

fof(f270,plain,
    ( spl9_13
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f276,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl9_13 ),
    inference(resolution,[],[f272,f65])).

fof(f65,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f272,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f270])).

fof(f567,plain,
    ( ~ spl9_7
    | ~ spl9_13 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f272,f132])).

fof(f132,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl9_7
  <=> ! [X10] : ~ r2_hidden(X10,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f251,plain,
    ( spl9_12
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f242,f81,f233])).

fof(f81,plain,
    ( spl9_3
  <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f242,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_3 ),
    inference(superposition,[],[f83,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f45,f54,f53,f53])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f83,plain,
    ( sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f146,plain,
    ( spl9_5
    | spl9_7
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f140,f81,f131,f124])).

fof(f140,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK2)
        | r2_hidden(X11,k2_enumset1(X11,X11,X11,X11)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f70,f101])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK2))
        | r2_hidden(X0,X2) )
    | ~ spl9_3 ),
    inference(superposition,[],[f61,f83])).

fof(f84,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f56,f81])).

fof(f56,plain,(
    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f32,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k2_relat_1(sK2) != k1_tarski(sK1)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k2_relat_1(sK2) != k1_tarski(sK1)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f79,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f55,f76,f72])).

fof(f55,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f54,f54])).

fof(f33,plain,
    ( k2_relat_1(sK2) != k1_tarski(sK1)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:30:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (9445)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (9433)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (9437)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (9453)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (9447)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (9439)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (9429)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (9457)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (9451)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (9455)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (9454)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (9443)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (9434)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (9456)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (9452)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (9445)Refutation not found, incomplete strategy% (9445)------------------------------
% 0.22/0.54  % (9445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9445)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9445)Memory used [KB]: 10618
% 0.22/0.54  % (9445)Time elapsed: 0.125 s
% 0.22/0.54  % (9445)------------------------------
% 0.22/0.54  % (9445)------------------------------
% 0.22/0.54  % (9431)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (9455)Refutation not found, incomplete strategy% (9455)------------------------------
% 0.22/0.54  % (9455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9455)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9455)Memory used [KB]: 6268
% 0.22/0.54  % (9455)Time elapsed: 0.121 s
% 0.22/0.54  % (9455)------------------------------
% 0.22/0.54  % (9455)------------------------------
% 0.22/0.54  % (9432)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (9430)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (9430)Refutation not found, incomplete strategy% (9430)------------------------------
% 0.22/0.54  % (9430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9430)Memory used [KB]: 1663
% 0.22/0.54  % (9430)Time elapsed: 0.135 s
% 0.22/0.54  % (9430)------------------------------
% 0.22/0.54  % (9430)------------------------------
% 0.22/0.55  % (9436)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (9446)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (9435)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (9458)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (9449)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (9458)Refutation not found, incomplete strategy% (9458)------------------------------
% 0.22/0.55  % (9458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9458)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9458)Memory used [KB]: 1663
% 0.22/0.55  % (9458)Time elapsed: 0.001 s
% 0.22/0.55  % (9458)------------------------------
% 0.22/0.55  % (9458)------------------------------
% 0.22/0.55  % (9448)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (9444)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (9450)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (9438)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (9441)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (9440)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (9442)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.02/0.65  % (9506)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.02/0.66  % (9505)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.02/0.67  % (9429)Refutation not found, incomplete strategy% (9429)------------------------------
% 2.02/0.67  % (9429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.67  % (9429)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.67  
% 2.02/0.67  % (9429)Memory used [KB]: 1663
% 2.02/0.67  % (9429)Time elapsed: 0.226 s
% 2.02/0.67  % (9429)------------------------------
% 2.02/0.67  % (9429)------------------------------
% 2.02/0.68  % (9512)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.02/0.68  % (9508)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.02/0.68  % (9432)Refutation not found, incomplete strategy% (9432)------------------------------
% 2.02/0.68  % (9432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.68  % (9432)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.68  
% 2.02/0.68  % (9432)Memory used [KB]: 6140
% 2.02/0.68  % (9432)Time elapsed: 0.267 s
% 2.02/0.68  % (9432)------------------------------
% 2.02/0.68  % (9432)------------------------------
% 3.25/0.82  % (9431)Time limit reached!
% 3.25/0.82  % (9431)------------------------------
% 3.25/0.82  % (9431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.82  % (9431)Termination reason: Time limit
% 3.25/0.82  
% 3.25/0.82  % (9431)Memory used [KB]: 7547
% 3.25/0.82  % (9431)Time elapsed: 0.407 s
% 3.25/0.82  % (9431)------------------------------
% 3.25/0.82  % (9431)------------------------------
% 3.25/0.82  % (9588)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.25/0.83  % (9453)Time limit reached!
% 3.25/0.83  % (9453)------------------------------
% 3.25/0.83  % (9453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.83  % (9453)Termination reason: Time limit
% 3.25/0.83  
% 3.25/0.83  % (9453)Memory used [KB]: 14839
% 3.25/0.83  % (9453)Time elapsed: 0.417 s
% 3.25/0.83  % (9453)------------------------------
% 3.25/0.83  % (9453)------------------------------
% 3.25/0.85  % (9596)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.90/0.90  % (9506)Refutation found. Thanks to Tanya!
% 3.90/0.90  % SZS status Theorem for theBenchmark
% 3.90/0.90  % SZS output start Proof for theBenchmark
% 3.90/0.90  fof(f3399,plain,(
% 3.90/0.90    $false),
% 3.90/0.90    inference(avatar_sat_refutation,[],[f79,f84,f146,f251,f567,f697,f2850,f3318,f3321,f3337,f3358,f3398])).
% 3.90/0.90  fof(f3398,plain,(
% 3.90/0.90    sK1 != sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.90/0.90    introduced(theory_tautology_sat_conflict,[])).
% 3.90/0.90  fof(f3358,plain,(
% 3.90/0.90    spl9_2 | ~spl9_5 | ~spl9_15 | ~spl9_106),
% 3.90/0.90    inference(avatar_contradiction_clause,[],[f3357])).
% 3.90/0.90  fof(f3357,plain,(
% 3.90/0.90    $false | (spl9_2 | ~spl9_5 | ~spl9_15 | ~spl9_106)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3356,f78])).
% 3.90/0.90  fof(f78,plain,(
% 3.90/0.90    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | spl9_2),
% 3.90/0.90    inference(avatar_component_clause,[],[f76])).
% 3.90/0.90  fof(f76,plain,(
% 3.90/0.90    spl9_2 <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.90/0.90  fof(f3356,plain,(
% 3.90/0.90    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | (~spl9_5 | ~spl9_15 | ~spl9_106)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3355,f125])).
% 3.90/0.90  fof(f125,plain,(
% 3.90/0.90    ( ! [X9] : (r2_hidden(X9,k2_enumset1(X9,X9,X9,X9))) ) | ~spl9_5),
% 3.90/0.90    inference(avatar_component_clause,[],[f124])).
% 3.90/0.90  fof(f124,plain,(
% 3.90/0.90    spl9_5 <=> ! [X9] : r2_hidden(X9,k2_enumset1(X9,X9,X9,X9))),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 3.90/0.90  fof(f3355,plain,(
% 3.90/0.90    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | (~spl9_15 | ~spl9_106)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3352,f287])).
% 3.90/0.90  fof(f287,plain,(
% 3.90/0.90    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl9_15),
% 3.90/0.90    inference(avatar_component_clause,[],[f285])).
% 3.90/0.90  fof(f285,plain,(
% 3.90/0.90    spl9_15 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 3.90/0.90  fof(f3352,plain,(
% 3.90/0.90    ~r2_hidden(sK1,k2_relat_1(sK2)) | ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl9_106),
% 3.90/0.90    inference(superposition,[],[f160,f3263])).
% 3.90/0.90  fof(f3263,plain,(
% 3.90/0.90    sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_106),
% 3.90/0.90    inference(avatar_component_clause,[],[f3261])).
% 3.90/0.90  fof(f3261,plain,(
% 3.90/0.90    spl9_106 <=> sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).
% 3.90/0.90  fof(f160,plain,(
% 3.90/0.90    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),k2_relat_1(X0)) | ~r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 3.90/0.90    inference(resolution,[],[f39,f66])).
% 3.90/0.90  fof(f66,plain,(
% 3.90/0.90    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.90/0.90    inference(equality_resolution,[],[f36])).
% 3.90/0.90  fof(f36,plain,(
% 3.90/0.90    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.90/0.90    inference(cnf_transformation,[],[f20])).
% 3.90/0.90  fof(f20,plain,(
% 3.90/0.90    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.90/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 3.90/0.90  fof(f17,plain,(
% 3.90/0.90    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f18,plain,(
% 3.90/0.90    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f19,plain,(
% 3.90/0.90    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f16,plain,(
% 3.90/0.90    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.90/0.90    inference(rectify,[],[f15])).
% 3.90/0.90  fof(f15,plain,(
% 3.90/0.90    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.90/0.90    inference(nnf_transformation,[],[f8])).
% 3.90/0.90  fof(f8,axiom,(
% 3.90/0.90    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 3.90/0.90  fof(f39,plain,(
% 3.90/0.90    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f20])).
% 3.90/0.90  fof(f3337,plain,(
% 3.90/0.90    spl9_111 | spl9_2 | ~spl9_12 | ~spl9_104),
% 3.90/0.90    inference(avatar_split_clause,[],[f3336,f3250,f233,f76,f3315])).
% 3.90/0.90  fof(f3315,plain,(
% 3.90/0.90    spl9_111 <=> r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2)),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).
% 3.90/0.90  fof(f233,plain,(
% 3.90/0.90    spl9_12 <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 3.90/0.90  fof(f3250,plain,(
% 3.90/0.90    spl9_104 <=> sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).
% 3.90/0.90  fof(f3336,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | (spl9_2 | ~spl9_12 | ~spl9_104)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3335,f301])).
% 3.90/0.90  fof(f301,plain,(
% 3.90/0.90    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(k4_tarski(sK0,X0),sK2)) ) | ~spl9_12),
% 3.90/0.90    inference(superposition,[],[f70,f235])).
% 3.90/0.90  fof(f235,plain,(
% 3.90/0.90    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_12),
% 3.90/0.90    inference(avatar_component_clause,[],[f233])).
% 3.90/0.90  fof(f70,plain,(
% 3.90/0.90    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3)) )),
% 3.90/0.90    inference(equality_resolution,[],[f62])).
% 3.90/0.90  fof(f62,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 3.90/0.90    inference(definition_unfolding,[],[f52,f54])).
% 3.90/0.90  fof(f54,plain,(
% 3.90/0.90    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.90/0.90    inference(definition_unfolding,[],[f34,f53])).
% 3.90/0.90  fof(f53,plain,(
% 3.90/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.90/0.90    inference(definition_unfolding,[],[f35,f44])).
% 3.90/0.90  fof(f44,plain,(
% 3.90/0.90    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f3])).
% 3.90/0.90  fof(f3,axiom,(
% 3.90/0.90    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.90/0.90  fof(f35,plain,(
% 3.90/0.90    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f2])).
% 3.90/0.90  fof(f2,axiom,(
% 3.90/0.90    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.90/0.90  fof(f34,plain,(
% 3.90/0.90    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f1])).
% 3.90/0.90  fof(f1,axiom,(
% 3.90/0.90    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.90/0.90  fof(f52,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 3.90/0.90    inference(cnf_transformation,[],[f30])).
% 3.90/0.90  fof(f30,plain,(
% 3.90/0.90    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 3.90/0.90    inference(flattening,[],[f29])).
% 3.90/0.90  fof(f29,plain,(
% 3.90/0.90    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 3.90/0.90    inference(nnf_transformation,[],[f4])).
% 3.90/0.90  fof(f4,axiom,(
% 3.90/0.90    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 3.90/0.90  fof(f3335,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl9_2 | ~spl9_104)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3334,f78])).
% 3.90/0.90  fof(f3334,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_104),
% 3.90/0.90    inference(superposition,[],[f38,f3252])).
% 3.90/0.90  fof(f3252,plain,(
% 3.90/0.90    sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_104),
% 3.90/0.90    inference(avatar_component_clause,[],[f3250])).
% 3.90/0.90  fof(f38,plain,(
% 3.90/0.90    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f20])).
% 3.90/0.90  fof(f3321,plain,(
% 3.90/0.90    spl9_106 | spl9_2 | ~spl9_12),
% 3.90/0.90    inference(avatar_split_clause,[],[f3320,f233,f76,f3261])).
% 3.90/0.90  fof(f3320,plain,(
% 3.90/0.90    sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl9_2 | ~spl9_12)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3319,f306])).
% 3.90/0.90  fof(f306,plain,(
% 3.90/0.90    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),sK2) | sK1 = X9) ) | ~spl9_12),
% 3.90/0.90    inference(superposition,[],[f60,f235])).
% 3.90/0.90  fof(f60,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 3.90/0.90    inference(definition_unfolding,[],[f48,f54])).
% 3.90/0.90  fof(f48,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 3.90/0.90    inference(cnf_transformation,[],[f28])).
% 3.90/0.90  fof(f28,plain,(
% 3.90/0.90    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 3.90/0.90    inference(flattening,[],[f27])).
% 3.90/0.90  fof(f27,plain,(
% 3.90/0.90    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 3.90/0.90    inference(nnf_transformation,[],[f5])).
% 3.90/0.90  fof(f5,axiom,(
% 3.90/0.90    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 3.90/0.90  fof(f3319,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl9_2 | ~spl9_12)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3300,f78])).
% 3.90/0.90  fof(f3300,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_12),
% 3.90/0.90    inference(resolution,[],[f301,f1225])).
% 3.90/0.90  fof(f1225,plain,(
% 3.90/0.90    ( ! [X0] : (r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | sK1 = sK3(sK2,X0)) ) | ~spl9_12),
% 3.90/0.90    inference(superposition,[],[f196,f235])).
% 3.90/0.90  fof(f196,plain,(
% 3.90/0.90    ( ! [X10,X11,X9] : (r2_hidden(sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11),X11) | k2_relat_1(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10))) = X11 | sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11) = X10) )),
% 3.90/0.90    inference(resolution,[],[f38,f60])).
% 3.90/0.90  fof(f3318,plain,(
% 3.90/0.90    spl9_104 | spl9_111 | spl9_2 | ~spl9_12),
% 3.90/0.90    inference(avatar_split_clause,[],[f3313,f233,f76,f3315,f3250])).
% 3.90/0.90  fof(f3313,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl9_2 | ~spl9_12)),
% 3.90/0.90    inference(subsumption_resolution,[],[f3299,f78])).
% 3.90/0.90  fof(f3299,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = sK4(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_12),
% 3.90/0.90    inference(resolution,[],[f301,f1258])).
% 3.90/0.90  fof(f1258,plain,(
% 3.90/0.90    ( ! [X0] : (r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | sK0 = sK4(sK2,X0)) ) | ~spl9_12),
% 3.90/0.90    inference(superposition,[],[f199,f235])).
% 3.90/0.90  fof(f199,plain,(
% 3.90/0.90    ( ! [X17,X18,X16] : (r2_hidden(sK3(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18),X18) | k2_relat_1(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17)) = X18 | sK4(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18) = X16) )),
% 3.90/0.90    inference(resolution,[],[f38,f64])).
% 3.90/0.90  fof(f64,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 3.90/0.90    inference(definition_unfolding,[],[f50,f54])).
% 3.90/0.90  fof(f50,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 3.90/0.90    inference(cnf_transformation,[],[f30])).
% 3.90/0.90  fof(f2850,plain,(
% 3.90/0.90    spl9_1 | ~spl9_12),
% 3.90/0.90    inference(avatar_split_clause,[],[f2849,f233,f72])).
% 3.90/0.90  fof(f72,plain,(
% 3.90/0.90    spl9_1 <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.90/0.90  fof(f2849,plain,(
% 3.90/0.90    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl9_12),
% 3.90/0.90    inference(subsumption_resolution,[],[f2795,f1163])).
% 3.90/0.90  fof(f1163,plain,(
% 3.90/0.90    ( ! [X0] : (~r2_hidden(sK6(sK2,X0),k2_enumset1(sK0,sK0,sK0,sK0)) | k1_relat_1(sK2) = X0 | ~r2_hidden(sK6(sK2,X0),X0)) ) | ~spl9_12),
% 3.90/0.90    inference(superposition,[],[f165,f235])).
% 3.90/0.90  fof(f165,plain,(
% 3.90/0.90    ( ! [X4,X2,X3] : (~r2_hidden(sK6(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)),X4),X4) | k1_relat_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) = X4 | ~r2_hidden(sK6(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)),X4),X2)) )),
% 3.90/0.90    inference(resolution,[],[f43,f69])).
% 3.90/0.90  fof(f69,plain,(
% 3.90/0.90    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 3.90/0.90    inference(equality_resolution,[],[f59])).
% 3.90/0.90  fof(f59,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 3.90/0.90    inference(definition_unfolding,[],[f49,f54])).
% 3.90/0.90  fof(f49,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f28])).
% 3.90/0.90  fof(f43,plain,(
% 3.90/0.90    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | k1_relat_1(X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f26])).
% 3.90/0.90  fof(f26,plain,(
% 3.90/0.90    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.90/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).
% 3.90/0.90  fof(f23,plain,(
% 3.90/0.90    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f24,plain,(
% 3.90/0.90    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f25,plain,(
% 3.90/0.90    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f22,plain,(
% 3.90/0.90    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.90/0.90    inference(rectify,[],[f21])).
% 3.90/0.90  fof(f21,plain,(
% 3.90/0.90    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.90/0.90    inference(nnf_transformation,[],[f7])).
% 3.90/0.90  fof(f7,axiom,(
% 3.90/0.90    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 3.90/0.90  fof(f2795,plain,(
% 3.90/0.90    r2_hidden(sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl9_12),
% 3.90/0.90    inference(factoring,[],[f1332])).
% 3.90/0.90  fof(f1332,plain,(
% 3.90/0.90    ( ! [X0] : (r2_hidden(sK6(sK2,X0),k2_enumset1(sK0,sK0,sK0,sK0)) | k1_relat_1(sK2) = X0 | r2_hidden(sK6(sK2,X0),X0)) ) | ~spl9_12),
% 3.90/0.90    inference(superposition,[],[f209,f235])).
% 3.90/0.90  fof(f209,plain,(
% 3.90/0.90    ( ! [X6,X8,X7] : (r2_hidden(sK6(k2_zfmisc_1(X6,k2_enumset1(X7,X7,X7,X7)),X8),X8) | k1_relat_1(k2_zfmisc_1(X6,k2_enumset1(X7,X7,X7,X7))) = X8 | r2_hidden(sK6(k2_zfmisc_1(X6,k2_enumset1(X7,X7,X7,X7)),X8),X6)) )),
% 3.90/0.90    inference(resolution,[],[f42,f61])).
% 3.90/0.90  fof(f61,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | r2_hidden(X0,X2)) )),
% 3.90/0.90    inference(definition_unfolding,[],[f47,f54])).
% 3.90/0.90  fof(f47,plain,(
% 3.90/0.90    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 3.90/0.90    inference(cnf_transformation,[],[f28])).
% 3.90/0.90  fof(f42,plain,(
% 3.90/0.90    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 3.90/0.90    inference(cnf_transformation,[],[f26])).
% 3.90/0.90  fof(f697,plain,(
% 3.90/0.90    spl9_15 | ~spl9_13),
% 3.90/0.90    inference(avatar_split_clause,[],[f276,f270,f285])).
% 3.90/0.90  fof(f270,plain,(
% 3.90/0.90    spl9_13 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 3.90/0.90  fof(f276,plain,(
% 3.90/0.90    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl9_13),
% 3.90/0.90    inference(resolution,[],[f272,f65])).
% 3.90/0.90  fof(f65,plain,(
% 3.90/0.90    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 3.90/0.90    inference(equality_resolution,[],[f37])).
% 3.90/0.90  fof(f37,plain,(
% 3.90/0.90    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.90/0.90    inference(cnf_transformation,[],[f20])).
% 3.90/0.90  fof(f272,plain,(
% 3.90/0.90    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_13),
% 3.90/0.90    inference(avatar_component_clause,[],[f270])).
% 3.90/0.90  fof(f567,plain,(
% 3.90/0.90    ~spl9_7 | ~spl9_13),
% 3.90/0.90    inference(avatar_contradiction_clause,[],[f548])).
% 3.90/0.90  fof(f548,plain,(
% 3.90/0.90    $false | (~spl9_7 | ~spl9_13)),
% 3.90/0.90    inference(subsumption_resolution,[],[f272,f132])).
% 3.90/0.90  fof(f132,plain,(
% 3.90/0.90    ( ! [X10] : (~r2_hidden(X10,sK2)) ) | ~spl9_7),
% 3.90/0.90    inference(avatar_component_clause,[],[f131])).
% 3.90/0.90  fof(f131,plain,(
% 3.90/0.90    spl9_7 <=> ! [X10] : ~r2_hidden(X10,sK2)),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 3.90/0.90  fof(f251,plain,(
% 3.90/0.90    spl9_12 | ~spl9_3),
% 3.90/0.90    inference(avatar_split_clause,[],[f242,f81,f233])).
% 3.90/0.90  fof(f81,plain,(
% 3.90/0.90    spl9_3 <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 3.90/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.90/0.90  fof(f242,plain,(
% 3.90/0.90    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_3),
% 3.90/0.90    inference(superposition,[],[f83,f58])).
% 3.90/0.90  fof(f58,plain,(
% 3.90/0.90    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 3.90/0.90    inference(definition_unfolding,[],[f45,f54,f53,f53])).
% 3.90/0.90  fof(f45,plain,(
% 3.90/0.90    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 3.90/0.90    inference(cnf_transformation,[],[f6])).
% 3.90/0.90  fof(f6,axiom,(
% 3.90/0.90    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 3.90/0.90  fof(f83,plain,(
% 3.90/0.90    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | ~spl9_3),
% 3.90/0.90    inference(avatar_component_clause,[],[f81])).
% 3.90/0.90  fof(f146,plain,(
% 3.90/0.90    spl9_5 | spl9_7 | ~spl9_3),
% 3.90/0.90    inference(avatar_split_clause,[],[f140,f81,f131,f124])).
% 3.90/0.90  fof(f140,plain,(
% 3.90/0.90    ( ! [X10,X11] : (~r2_hidden(X10,sK2) | r2_hidden(X11,k2_enumset1(X11,X11,X11,X11))) ) | ~spl9_3),
% 3.90/0.90    inference(resolution,[],[f70,f101])).
% 3.90/0.90  fof(f101,plain,(
% 3.90/0.90    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK2)) | r2_hidden(X0,X2)) ) | ~spl9_3),
% 3.90/0.90    inference(superposition,[],[f61,f83])).
% 3.90/0.90  fof(f84,plain,(
% 3.90/0.90    spl9_3),
% 3.90/0.90    inference(avatar_split_clause,[],[f56,f81])).
% 3.90/0.90  fof(f56,plain,(
% 3.90/0.90    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 3.90/0.90    inference(definition_unfolding,[],[f32,f54])).
% 3.90/0.90  fof(f32,plain,(
% 3.90/0.90    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 3.90/0.90    inference(cnf_transformation,[],[f14])).
% 3.90/0.90  fof(f14,plain,(
% 3.90/0.90    (k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 3.90/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 3.90/0.90  fof(f13,plain,(
% 3.90/0.90    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 3.90/0.90    introduced(choice_axiom,[])).
% 3.90/0.90  fof(f12,plain,(
% 3.90/0.90    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 3.90/0.90    inference(flattening,[],[f11])).
% 3.90/0.90  fof(f11,plain,(
% 3.90/0.90    ? [X0,X1,X2] : (((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 3.90/0.90    inference(ennf_transformation,[],[f10])).
% 3.90/0.90  fof(f10,negated_conjecture,(
% 3.90/0.90    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 3.90/0.90    inference(negated_conjecture,[],[f9])).
% 3.90/0.90  fof(f9,conjecture,(
% 3.90/0.90    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 3.90/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 3.90/0.90  fof(f79,plain,(
% 3.90/0.90    ~spl9_1 | ~spl9_2),
% 3.90/0.90    inference(avatar_split_clause,[],[f55,f76,f72])).
% 3.90/0.90  fof(f55,plain,(
% 3.90/0.90    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.90/0.90    inference(definition_unfolding,[],[f33,f54,f54])).
% 3.90/0.90  fof(f33,plain,(
% 3.90/0.90    k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 3.90/0.90    inference(cnf_transformation,[],[f14])).
% 3.90/0.90  % SZS output end Proof for theBenchmark
% 3.90/0.90  % (9506)------------------------------
% 3.90/0.90  % (9506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.90/0.90  % (9506)Termination reason: Refutation
% 3.90/0.90  
% 3.90/0.90  % (9506)Memory used [KB]: 12920
% 3.90/0.90  % (9506)Time elapsed: 0.290 s
% 3.90/0.90  % (9506)------------------------------
% 3.90/0.90  % (9506)------------------------------
% 3.90/0.91  % (9427)Success in time 0.539 s
%------------------------------------------------------------------------------
