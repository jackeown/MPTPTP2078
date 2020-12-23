%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 248 expanded)
%              Number of leaves         :   33 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 576 expanded)
%              Number of equality atoms :   81 ( 161 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f58,f59,f60,f71,f76,f98,f99,f100,f107,f114,f137,f138,f139,f147,f152,f172,f182,f196,f201,f211,f221,f232,f246])).

fof(f246,plain,
    ( ~ spl7_11
    | spl7_17
    | ~ spl7_19
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl7_11
    | spl7_17
    | ~ spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f244,f113])).

fof(f113,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_11
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f244,plain,
    ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | spl7_17
    | ~ spl7_19
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f240,f181])).

fof(f181,plain,
    ( k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl7_19
  <=> k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f240,plain,
    ( sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0))
    | spl7_17
    | ~ spl7_23 ),
    inference(superposition,[],[f157,f222])).

fof(f222,plain,
    ( ! [X0,X1] : k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) = k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),X0),X1)
    | ~ spl7_23 ),
    inference(superposition,[],[f31,f220])).

fof(f220,plain,
    ( k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_23
  <=> k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f157,plain,
    ( sK0 != k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl7_17
  <=> sK0 = k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f232,plain,
    ( ~ spl7_17
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f228,f128,f123,f84,f44,f155])).

fof(f44,plain,
    ( spl7_2
  <=> r2_hidden(k2_mcart_1(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f84,plain,
    ( spl7_7
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f123,plain,
    ( spl7_12
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f128,plain,
    ( spl7_13
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f228,plain,
    ( sK0 != k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0))
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f130,f125,f185])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK2)
        | sK0 != k4_tarski(k3_mcart_1(X0,X1,k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(resolution,[],[f61,f86])).

fof(f86,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,sK3)
        | sK0 != k4_tarski(k3_mcart_1(X0,X1,X2),k2_mcart_1(sK0))
        | ~ r2_hidden(X1,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f29,f46])).

fof(f46,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f29,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(X8,sK4)
      | sK0 != k4_tarski(k3_mcart_1(X5,X6,X7),X8)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f18,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK0
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK0
        | ~ r2_hidden(X8,sK4)
        | ~ r2_hidden(X7,sK3)
        | ~ r2_hidden(X6,sK2)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13])).

% (1911)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK0
          | ~ r2_hidden(X8,sK4)
          | ~ r2_hidden(X7,sK3)
          | ~ r2_hidden(X6,sK2)
          | ~ r2_hidden(X5,sK1) )
      & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f125,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f221,plain,
    ( spl7_23
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f215,f208,f198,f218])).

fof(f198,plain,
    ( spl7_21
  <=> sK6(k1_mcart_1(k1_mcart_1(sK0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f208,plain,
    ( spl7_22
  <=> k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f215,plain,
    ( k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))))
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f210,f200])).

fof(f200,plain,
    ( sK6(k1_mcart_1(k1_mcart_1(sK0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f198])).

fof(f210,plain,
    ( k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f211,plain,
    ( spl7_22
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f205,f193,f133,f208])).

fof(f133,plain,
    ( spl7_14
  <=> k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f193,plain,
    ( spl7_20
  <=> sK5(k1_mcart_1(k1_mcart_1(sK0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f205,plain,
    ( k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f135,f195])).

fof(f195,plain,
    ( sK5(k1_mcart_1(k1_mcart_1(sK0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f135,plain,
    ( k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f201,plain,
    ( spl7_21
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f191,f133,f198])).

fof(f191,plain,
    ( sK6(k1_mcart_1(k1_mcart_1(sK0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))
    | ~ spl7_14 ),
    inference(superposition,[],[f20,f135])).

fof(f20,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f196,plain,
    ( spl7_20
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f190,f133,f193])).

fof(f190,plain,
    ( sK5(k1_mcart_1(k1_mcart_1(sK0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))
    | ~ spl7_14 ),
    inference(superposition,[],[f19,f135])).

fof(f19,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f182,plain,
    ( spl7_19
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f176,f169,f149,f179])).

fof(f149,plain,
    ( spl7_16
  <=> sK6(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f169,plain,
    ( spl7_18
  <=> k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f176,plain,
    ( k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(backward_demodulation,[],[f171,f151])).

fof(f151,plain,
    ( sK6(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f171,plain,
    ( k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f172,plain,
    ( spl7_18
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f166,f144,f94,f169])).

fof(f94,plain,
    ( spl7_9
  <=> k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f144,plain,
    ( spl7_15
  <=> sK5(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f166,plain,
    ( k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f96,f146])).

fof(f146,plain,
    ( sK5(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f96,plain,
    ( k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f152,plain,
    ( spl7_16
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f142,f94,f149])).

fof(f142,plain,
    ( sK6(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0))
    | ~ spl7_9 ),
    inference(superposition,[],[f20,f96])).

fof(f147,plain,
    ( spl7_15
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f141,f94,f144])).

fof(f141,plain,
    ( sK5(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0))
    | ~ spl7_9 ),
    inference(superposition,[],[f19,f96])).

fof(f139,plain,
    ( spl7_12
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f121,f89,f123])).

fof(f89,plain,
    ( spl7_8
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f121,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f91,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f91,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f138,plain,
    ( spl7_13
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f120,f89,f128])).

fof(f120,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1)
    | ~ spl7_8 ),
    inference(resolution,[],[f91,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f137,plain,
    ( spl7_14
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f119,f89,f133])).

fof(f119,plain,
    ( k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))
    | ~ spl7_8 ),
    inference(resolution,[],[f91,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f114,plain,
    ( spl7_11
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f109,f104,f73,f111])).

% (1906)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f73,plain,
    ( spl7_6
  <=> sK6(sK0) = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f104,plain,
    ( spl7_10
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f109,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f106,f75])).

fof(f75,plain,
    ( sK6(sK0) = k2_mcart_1(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f106,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( spl7_10
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f101,f68,f54,f104])).

fof(f54,plain,
    ( spl7_4
  <=> sK0 = k4_tarski(sK5(sK0),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f68,plain,
    ( spl7_5
  <=> sK5(sK0) = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f101,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f56,f70])).

fof(f70,plain,
    ( sK5(sK0) = k1_mcart_1(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f56,plain,
    ( sK0 = k4_tarski(sK5(sK0),sK6(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f100,plain,
    ( spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f82,f49,f84])).

fof(f49,plain,
    ( spl7_3
  <=> r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f82,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f23])).

fof(f51,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f99,plain,
    ( spl7_8
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f81,f49,f89])).

fof(f81,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f22])).

fof(f98,plain,
    ( spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f80,f49,f94])).

fof(f80,plain,
    ( k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f24])).

fof(f76,plain,
    ( spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f66,f54,f73])).

fof(f66,plain,
    ( sK6(sK0) = k2_mcart_1(sK0)
    | ~ spl7_4 ),
    inference(superposition,[],[f20,f56])).

fof(f71,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f65,f54,f68])).

fof(f65,plain,
    ( sK5(sK0) = k1_mcart_1(sK0)
    | ~ spl7_4 ),
    inference(superposition,[],[f19,f56])).

fof(f60,plain,
    ( spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f42,f33,f44])).

fof(f33,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f42,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f35,f23])).

fof(f35,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f59,plain,
    ( spl7_3
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f41,f33,f49])).

fof(f41,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl7_1 ),
    inference(resolution,[],[f35,f22])).

fof(f58,plain,
    ( spl7_4
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f40,f33,f54])).

fof(f40,plain,
    ( sK0 = k4_tarski(sK5(sK0),sK6(sK0))
    | ~ spl7_1 ),
    inference(resolution,[],[f35,f24])).

fof(f36,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f30,f33])).

fof(f30,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f17,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (1924)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (1908)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (1928)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (1916)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (1898)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (1898)Refutation not found, incomplete strategy% (1898)------------------------------
% 0.20/0.51  % (1898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1898)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1898)Memory used [KB]: 1663
% 0.20/0.51  % (1898)Time elapsed: 0.105 s
% 0.20/0.51  % (1898)------------------------------
% 0.20/0.51  % (1898)------------------------------
% 0.20/0.51  % (1916)Refutation not found, incomplete strategy% (1916)------------------------------
% 0.20/0.51  % (1916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1916)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1916)Memory used [KB]: 10618
% 0.20/0.51  % (1916)Time elapsed: 0.107 s
% 0.20/0.51  % (1916)------------------------------
% 0.20/0.51  % (1916)------------------------------
% 0.20/0.51  % (1904)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (1908)Refutation not found, incomplete strategy% (1908)------------------------------
% 0.20/0.51  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1908)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (1908)Memory used [KB]: 10618
% 0.20/0.52  % (1908)Time elapsed: 0.109 s
% 0.20/0.52  % (1908)------------------------------
% 0.20/0.52  % (1908)------------------------------
% 0.20/0.52  % (1905)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (1924)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f249,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f36,f58,f59,f60,f71,f76,f98,f99,f100,f107,f114,f137,f138,f139,f147,f152,f172,f182,f196,f201,f211,f221,f232,f246])).
% 0.20/0.52  fof(f246,plain,(
% 0.20/0.52    ~spl7_11 | spl7_17 | ~spl7_19 | ~spl7_23),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f245])).
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    $false | (~spl7_11 | spl7_17 | ~spl7_19 | ~spl7_23)),
% 0.20/0.52    inference(subsumption_resolution,[],[f244,f113])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) | ~spl7_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f111])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl7_11 <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) | (spl7_17 | ~spl7_19 | ~spl7_23)),
% 0.20/0.52    inference(forward_demodulation,[],[f240,f181])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) | ~spl7_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f179])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    spl7_19 <=> k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0)) | (spl7_17 | ~spl7_23)),
% 0.20/0.52    inference(superposition,[],[f157,f222])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) = k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),X0),X1)) ) | ~spl7_23),
% 0.20/0.52    inference(superposition,[],[f31,f220])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))) | ~spl7_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f218])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    spl7_23 <=> k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    sK0 != k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0)) | spl7_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl7_17 <=> sK0 = k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ~spl7_17 | ~spl7_2 | ~spl7_7 | ~spl7_12 | ~spl7_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f228,f128,f123,f84,f44,f155])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    spl7_2 <=> r2_hidden(k2_mcart_1(sK0),sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl7_7 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl7_12 <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    spl7_13 <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    sK0 != k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0)) | (~spl7_2 | ~spl7_7 | ~spl7_12 | ~spl7_13)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f130,f125,f185])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | sK0 != k4_tarski(k3_mcart_1(X0,X1,k2_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(sK0)) | ~r2_hidden(X0,sK1)) ) | (~spl7_2 | ~spl7_7)),
% 0.20/0.52    inference(resolution,[],[f61,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) | ~spl7_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK3) | sK0 != k4_tarski(k3_mcart_1(X0,X1,X2),k2_mcart_1(sK0)) | ~r2_hidden(X1,sK2) | ~r2_hidden(X0,sK1)) ) | ~spl7_2),
% 0.20/0.52    inference(resolution,[],[f29,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK0),sK4) | ~spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f44])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X6,X8,X7,X5] : (~r2_hidden(X8,sK4) | sK0 != k4_tarski(k3_mcart_1(X5,X6,X7),X8) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f18,f26])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X6,X8,X7,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13])).
% 0.20/0.52  % (1911)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4))) => (! [X8,X7,X6,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2) | ~spl7_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1) | ~spl7_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f128])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    spl7_23 | ~spl7_21 | ~spl7_22),
% 0.20/0.52    inference(avatar_split_clause,[],[f215,f208,f198,f218])).
% 0.20/0.52  fof(f198,plain,(
% 0.20/0.52    spl7_21 <=> sK6(k1_mcart_1(k1_mcart_1(sK0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    spl7_22 <=> k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))) | (~spl7_21 | ~spl7_22)),
% 0.20/0.52    inference(backward_demodulation,[],[f210,f200])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    sK6(k1_mcart_1(k1_mcart_1(sK0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) | ~spl7_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f198])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) | ~spl7_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f208])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    spl7_22 | ~spl7_14 | ~spl7_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f205,f193,f133,f208])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl7_14 <=> k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl7_20 <=> sK5(k1_mcart_1(k1_mcart_1(sK0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) | (~spl7_14 | ~spl7_20)),
% 0.20/0.52    inference(backward_demodulation,[],[f135,f195])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    sK5(k1_mcart_1(k1_mcart_1(sK0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) | ~spl7_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f193])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) | ~spl7_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f133])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    spl7_21 | ~spl7_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f191,f133,f198])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    sK6(k1_mcart_1(k1_mcart_1(sK0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) | ~spl7_14),
% 0.20/0.52    inference(superposition,[],[f20,f135])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    spl7_20 | ~spl7_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f190,f133,f193])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    sK5(k1_mcart_1(k1_mcart_1(sK0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) | ~spl7_14),
% 0.20/0.52    inference(superposition,[],[f19,f135])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    spl7_19 | ~spl7_16 | ~spl7_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f176,f169,f149,f179])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    spl7_16 <=> sK6(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    spl7_18 <=> k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) | (~spl7_16 | ~spl7_18)),
% 0.20/0.52    inference(backward_demodulation,[],[f171,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    sK6(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0)) | ~spl7_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f149])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) | ~spl7_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f169])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    spl7_18 | ~spl7_9 | ~spl7_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f166,f144,f94,f169])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl7_9 <=> k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl7_15 <=> sK5(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) | (~spl7_9 | ~spl7_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f96,f146])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    sK5(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0)) | ~spl7_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f144])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) | ~spl7_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f94])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    spl7_16 | ~spl7_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f142,f94,f149])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    sK6(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0)) | ~spl7_9),
% 0.20/0.52    inference(superposition,[],[f20,f96])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    spl7_15 | ~spl7_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f141,f94,f144])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    sK5(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0)) | ~spl7_9),
% 0.20/0.52    inference(superposition,[],[f19,f96])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    spl7_12 | ~spl7_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f121,f89,f123])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    spl7_8 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2) | ~spl7_8),
% 0.20/0.52    inference(resolution,[],[f91,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2)) | ~spl7_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f89])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    spl7_13 | ~spl7_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f120,f89,f128])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1) | ~spl7_8),
% 0.20/0.52    inference(resolution,[],[f91,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    spl7_14 | ~spl7_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f119,f89,f133])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) | ~spl7_8),
% 0.20/0.52    inference(resolution,[],[f91,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK5(X0),sK6(X0)) = X0)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    spl7_11 | ~spl7_6 | ~spl7_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f109,f104,f73,f111])).
% 0.20/0.52  % (1906)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl7_6 <=> sK6(sK0) = k2_mcart_1(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    spl7_10 <=> sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) | (~spl7_6 | ~spl7_10)),
% 0.20/0.52    inference(forward_demodulation,[],[f106,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    sK6(sK0) = k2_mcart_1(sK0) | ~spl7_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0)) | ~spl7_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f104])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    spl7_10 | ~spl7_4 | ~spl7_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f101,f68,f54,f104])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl7_4 <=> sK0 = k4_tarski(sK5(sK0),sK6(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl7_5 <=> sK5(sK0) = k1_mcart_1(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0)) | (~spl7_4 | ~spl7_5)),
% 0.20/0.52    inference(backward_demodulation,[],[f56,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    sK5(sK0) = k1_mcart_1(sK0) | ~spl7_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f54])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl7_7 | ~spl7_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f82,f49,f84])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl7_3 <=> r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) | ~spl7_3),
% 0.20/0.52    inference(resolution,[],[f51,f23])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl7_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f49])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    spl7_8 | ~spl7_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f81,f49,f89])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2)) | ~spl7_3),
% 0.20/0.52    inference(resolution,[],[f51,f22])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    spl7_9 | ~spl7_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f80,f49,f94])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) | ~spl7_3),
% 0.20/0.52    inference(resolution,[],[f51,f24])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl7_6 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f66,f54,f73])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    sK6(sK0) = k2_mcart_1(sK0) | ~spl7_4),
% 0.20/0.52    inference(superposition,[],[f20,f56])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl7_5 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f65,f54,f68])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    sK5(sK0) = k1_mcart_1(sK0) | ~spl7_4),
% 0.20/0.52    inference(superposition,[],[f19,f56])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl7_2 | ~spl7_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f33,f44])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    spl7_1 <=> r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK0),sK4) | ~spl7_1),
% 0.20/0.52    inference(resolution,[],[f35,f23])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) | ~spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f33])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl7_3 | ~spl7_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f33,f49])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl7_1),
% 0.20/0.52    inference(resolution,[],[f35,f22])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl7_4 | ~spl7_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f33,f54])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) | ~spl7_1),
% 0.20/0.52    inference(resolution,[],[f35,f24])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    spl7_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f33])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.20/0.52    inference(definition_unfolding,[],[f17,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (1924)------------------------------
% 0.20/0.52  % (1924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1924)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (1924)Memory used [KB]: 6396
% 0.20/0.52  % (1924)Time elapsed: 0.116 s
% 0.20/0.52  % (1924)------------------------------
% 0.20/0.52  % (1924)------------------------------
% 0.20/0.52  % (1897)Success in time 0.159 s
%------------------------------------------------------------------------------
