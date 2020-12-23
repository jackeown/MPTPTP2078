%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0734+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 6.59s
% Output     : Refutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 581 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7302,f7348,f7511])).

fof(f7511,plain,(
    ~ spl290_14 ),
    inference(avatar_contradiction_clause,[],[f7366])).

fof(f7366,plain,
    ( $false
    | ~ spl290_14 ),
    inference(unit_resulting_resolution,[],[f4888,f2905,f2906,f7363,f4082])).

fof(f4082,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f1798])).

fof(f1798,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_ordinal1(X2) ) ),
    inference(flattening,[],[f1797])).

fof(f1797,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f1068])).

fof(f1068,axiom,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

fof(f7363,plain,
    ( r2_hidden(sK65,sK66)
    | ~ spl290_14 ),
    inference(subsumption_resolution,[],[f7362,f2901])).

fof(f2901,plain,(
    v1_ordinal1(sK65) ),
    inference(cnf_transformation,[],[f2216])).

fof(f2216,plain,
    ( ~ r2_hidden(sK65,sK67)
    & r2_hidden(sK66,sK67)
    & r1_tarski(sK65,sK66)
    & v3_ordinal1(sK67)
    & v3_ordinal1(sK66)
    & v1_ordinal1(sK65) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK65,sK66,sK67])],[f1093,f2215,f2214,f2213])).

fof(f2213,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK65,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK65,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK65) ) ),
    introduced(choice_axiom,[])).

fof(f2214,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(sK65,X2)
            & r2_hidden(X1,X2)
            & r1_tarski(sK65,X1)
            & v3_ordinal1(X2) )
        & v3_ordinal1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK65,X2)
          & r2_hidden(sK66,X2)
          & r1_tarski(sK65,sK66)
          & v3_ordinal1(X2) )
      & v3_ordinal1(sK66) ) ),
    introduced(choice_axiom,[])).

fof(f2215,plain,
    ( ? [X2] :
        ( ~ r2_hidden(sK65,X2)
        & r2_hidden(sK66,X2)
        & r1_tarski(sK65,sK66)
        & v3_ordinal1(X2) )
   => ( ~ r2_hidden(sK65,sK67)
      & r2_hidden(sK66,sK67)
      & r1_tarski(sK65,sK66)
      & v3_ordinal1(sK67) ) ),
    introduced(choice_axiom,[])).

fof(f1093,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f1092])).

fof(f1092,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1071])).

fof(f1071,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1070])).

fof(f1070,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f7362,plain,
    ( r2_hidden(sK65,sK66)
    | ~ v1_ordinal1(sK65)
    | ~ spl290_14 ),
    inference(subsumption_resolution,[],[f7351,f2902])).

fof(f2902,plain,(
    v3_ordinal1(sK66) ),
    inference(cnf_transformation,[],[f2216])).

fof(f7351,plain,
    ( r2_hidden(sK65,sK66)
    | ~ v3_ordinal1(sK66)
    | ~ v1_ordinal1(sK65)
    | ~ spl290_14 ),
    inference(resolution,[],[f7301,f3004])).

fof(f3004,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1109])).

fof(f1109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f1108])).

fof(f1108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1069])).

fof(f1069,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f7301,plain,
    ( r2_xboole_0(sK65,sK66)
    | ~ spl290_14 ),
    inference(avatar_component_clause,[],[f7300])).

fof(f7300,plain,
    ( spl290_14
  <=> r2_xboole_0(sK65,sK66) ),
    introduced(avatar_definition,[new_symbols(naming,[spl290_14])])).

fof(f2906,plain,(
    ~ r2_hidden(sK65,sK67) ),
    inference(cnf_transformation,[],[f2216])).

fof(f2905,plain,(
    r2_hidden(sK66,sK67) ),
    inference(cnf_transformation,[],[f2216])).

fof(f4888,plain,(
    v1_ordinal1(sK67) ),
    inference(resolution,[],[f2903,f3008])).

fof(f3008,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1112])).

fof(f1112,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1054])).

fof(f1054,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f2903,plain,(
    v3_ordinal1(sK67) ),
    inference(cnf_transformation,[],[f2216])).

fof(f7348,plain,(
    ~ spl290_13 ),
    inference(avatar_contradiction_clause,[],[f7347])).

fof(f7347,plain,
    ( $false
    | ~ spl290_13 ),
    inference(subsumption_resolution,[],[f7305,f2906])).

fof(f7305,plain,
    ( r2_hidden(sK65,sK67)
    | ~ spl290_13 ),
    inference(superposition,[],[f2905,f7281])).

fof(f7281,plain,
    ( sK65 = sK66
    | ~ spl290_13 ),
    inference(avatar_component_clause,[],[f7280])).

fof(f7280,plain,
    ( spl290_13
  <=> sK65 = sK66 ),
    introduced(avatar_definition,[new_symbols(naming,[spl290_13])])).

fof(f7302,plain,
    ( spl290_14
    | spl290_13 ),
    inference(avatar_split_clause,[],[f4923,f7280,f7300])).

fof(f4923,plain,
    ( sK65 = sK66
    | r2_xboole_0(sK65,sK66) ),
    inference(resolution,[],[f2904,f3916])).

fof(f3916,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2596])).

fof(f2596,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f2595])).

fof(f2595,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f2904,plain,(
    r1_tarski(sK65,sK66) ),
    inference(cnf_transformation,[],[f2216])).
%------------------------------------------------------------------------------
