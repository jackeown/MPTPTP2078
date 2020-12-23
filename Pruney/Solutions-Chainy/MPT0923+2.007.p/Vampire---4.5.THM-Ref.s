%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 213 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  176 ( 700 expanded)
%              Number of equality atoms :   44 ( 160 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f172,f176,f179,f183])).

fof(f183,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f181,f45])).

fof(f45,plain,(
    r2_hidden(k2_mcart_1(sK0),sK4) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f37,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f21,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK0
        | ~ r2_hidden(X8,sK4)
        | ~ r2_hidden(X7,sK3)
        | ~ r2_hidden(X6,sK2)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f15])).

fof(f15,plain,
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

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f181,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK4)
    | ~ spl10_16 ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( sK0 != sK0
    | ~ r2_hidden(k2_mcart_1(sK0),sK4)
    | ~ spl10_16 ),
    inference(superposition,[],[f155,f62])).

fof(f62,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(backward_demodulation,[],[f61,f48])).

fof(f48,plain,(
    sK6(sK0) = k2_mcart_1(sK0) ),
    inference(superposition,[],[f24,f43])).

fof(f43,plain,(
    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f61,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0)) ),
    inference(backward_demodulation,[],[f43,f47])).

fof(f47,plain,(
    sK5(sK0) = k1_mcart_1(sK0) ),
    inference(superposition,[],[f23,f43])).

fof(f23,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f155,plain,
    ( ! [X0] :
        ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_16
  <=> ! [X0] :
        ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
        | ~ r2_hidden(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f179,plain,(
    spl10_14 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl10_14 ),
    inference(subsumption_resolution,[],[f177,f44])).

fof(f44,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f177,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | spl10_14 ),
    inference(resolution,[],[f148,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X2,X3),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X2,X3),X2)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k3_mcart_1(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)) = X0
        & r2_hidden(sK9(X0,X1,X2,X3),X3)
        & r2_hidden(sK8(X0,X1,X2,X3),X2)
        & r2_hidden(sK7(X0,X1,X2,X3),X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f14,f19])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k3_mcart_1(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)) = X0
        & r2_hidden(sK9(X0,X1,X2,X3),X3)
        & r2_hidden(sK8(X0,X1,X2,X3),X2)
        & r2_hidden(sK7(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f148,plain,
    ( ~ r2_hidden(sK8(k1_mcart_1(sK0),sK1,sK2,sK3),sK2)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl10_14
  <=> r2_hidden(sK8(k1_mcart_1(sK0),sK1,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f176,plain,(
    spl10_13 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl10_13 ),
    inference(subsumption_resolution,[],[f174,f44])).

fof(f174,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | spl10_13 ),
    inference(resolution,[],[f144,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X2,X3),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X2,X3),X1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f144,plain,
    ( ~ r2_hidden(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK1)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl10_13
  <=> r2_hidden(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f172,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl10_15 ),
    inference(subsumption_resolution,[],[f170,f69])).

fof(f69,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) ),
    inference(resolution,[],[f44,f28])).

fof(f170,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)
    | spl10_15 ),
    inference(forward_demodulation,[],[f152,f140])).

fof(f140,plain,(
    sK9(k1_mcart_1(sK0),sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f24,f66])).

fof(f66,plain,(
    k1_mcart_1(sK0) = k4_tarski(k4_tarski(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK8(k1_mcart_1(sK0),sK1,sK2,sK3)),sK9(k1_mcart_1(sK0),sK1,sK2,sK3)) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
      | k4_tarski(k4_tarski(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3)),sK9(X0,X1,X2,X3)) = X0 ) ),
    inference(definition_unfolding,[],[f35,f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f152,plain,
    ( ~ r2_hidden(sK9(k1_mcart_1(sK0),sK1,sK2,sK3),sK3)
    | spl10_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_15
  <=> r2_hidden(sK9(k1_mcart_1(sK0),sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f156,plain,
    ( ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16 ),
    inference(avatar_split_clause,[],[f137,f154,f150,f146,f142])).

fof(f137,plain,(
    ! [X0] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(sK9(k1_mcart_1(sK0),sK1,sK2,sK3),sK3)
      | ~ r2_hidden(sK8(k1_mcart_1(sK0),sK1,sK2,sK3),sK2)
      | ~ r2_hidden(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK1) ) ),
    inference(superposition,[],[f36,f66])).

fof(f36,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f22,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK0
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:13:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.43  % (9475)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.44  % (9471)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.44  % (9471)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.45  % (9479)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f184,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(avatar_sat_refutation,[],[f156,f172,f176,f179,f183])).
% 0.18/0.45  fof(f183,plain,(
% 0.18/0.45    ~spl10_16),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f182])).
% 0.18/0.45  fof(f182,plain,(
% 0.18/0.45    $false | ~spl10_16),
% 0.18/0.45    inference(subsumption_resolution,[],[f181,f45])).
% 0.18/0.45  fof(f45,plain,(
% 0.18/0.45    r2_hidden(k2_mcart_1(sK0),sK4)),
% 0.18/0.45    inference(resolution,[],[f37,f28])).
% 0.18/0.45  fof(f28,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  fof(f12,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.45    inference(ennf_transformation,[],[f4])).
% 0.18/0.45  fof(f4,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.18/0.45  fof(f37,plain,(
% 0.18/0.45    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.18/0.45    inference(definition_unfolding,[],[f21,f30])).
% 0.18/0.45  fof(f30,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f6])).
% 0.18/0.45  fof(f6,axiom,(
% 0.18/0.45    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.18/0.45  fof(f21,plain,(
% 0.18/0.45    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  fof(f16,plain,(
% 0.18/0.45    ! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f15])).
% 0.18/0.45  fof(f15,plain,(
% 0.18/0.45    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4))) => (! [X8,X7,X6,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f11,plain,(
% 0.18/0.45    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.18/0.45    inference(ennf_transformation,[],[f10])).
% 0.18/0.45  fof(f10,negated_conjecture,(
% 0.18/0.45    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.18/0.45    inference(negated_conjecture,[],[f9])).
% 0.18/0.45  fof(f9,conjecture,(
% 0.18/0.45    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.18/0.45  fof(f181,plain,(
% 0.18/0.45    ~r2_hidden(k2_mcart_1(sK0),sK4) | ~spl10_16),
% 0.18/0.45    inference(trivial_inequality_removal,[],[f180])).
% 0.18/0.45  fof(f180,plain,(
% 0.18/0.45    sK0 != sK0 | ~r2_hidden(k2_mcart_1(sK0),sK4) | ~spl10_16),
% 0.18/0.45    inference(superposition,[],[f155,f62])).
% 0.18/0.45  fof(f62,plain,(
% 0.18/0.45    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.18/0.45    inference(backward_demodulation,[],[f61,f48])).
% 0.18/0.45  fof(f48,plain,(
% 0.18/0.45    sK6(sK0) = k2_mcart_1(sK0)),
% 0.18/0.45    inference(superposition,[],[f24,f43])).
% 0.18/0.45  fof(f43,plain,(
% 0.18/0.45    sK0 = k4_tarski(sK5(sK0),sK6(sK0))),
% 0.18/0.45    inference(resolution,[],[f37,f29])).
% 0.18/0.45  fof(f29,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f18,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f17])).
% 0.18/0.45  fof(f17,plain,(
% 0.18/0.45    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK5(X0),sK6(X0)) = X0)),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f13,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.45    inference(ennf_transformation,[],[f1])).
% 0.18/0.45  fof(f1,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.18/0.45  fof(f24,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.18/0.45    inference(cnf_transformation,[],[f8])).
% 0.18/0.45  fof(f8,axiom,(
% 0.18/0.45    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.18/0.45  fof(f61,plain,(
% 0.18/0.45    sK0 = k4_tarski(k1_mcart_1(sK0),sK6(sK0))),
% 0.18/0.45    inference(backward_demodulation,[],[f43,f47])).
% 0.18/0.45  fof(f47,plain,(
% 0.18/0.45    sK5(sK0) = k1_mcart_1(sK0)),
% 0.18/0.45    inference(superposition,[],[f23,f43])).
% 0.18/0.45  fof(f23,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.18/0.45    inference(cnf_transformation,[],[f8])).
% 0.18/0.45  fof(f155,plain,(
% 0.18/0.45    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK4)) ) | ~spl10_16),
% 0.18/0.45    inference(avatar_component_clause,[],[f154])).
% 0.18/0.45  fof(f154,plain,(
% 0.18/0.45    spl10_16 <=> ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK4))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.18/0.45  fof(f179,plain,(
% 0.18/0.45    spl10_14),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f178])).
% 0.18/0.45  fof(f178,plain,(
% 0.18/0.45    $false | spl10_14),
% 0.18/0.45    inference(subsumption_resolution,[],[f177,f44])).
% 0.18/0.45  fof(f44,plain,(
% 0.18/0.45    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.18/0.45    inference(resolution,[],[f37,f27])).
% 0.18/0.45  fof(f27,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  fof(f177,plain,(
% 0.18/0.45    ~r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | spl10_14),
% 0.18/0.45    inference(resolution,[],[f148,f40])).
% 0.18/0.45  fof(f40,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X2,X3),X2) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.18/0.45    inference(definition_unfolding,[],[f33,f25])).
% 0.18/0.45  fof(f25,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f3])).
% 0.18/0.45  fof(f3,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.18/0.45  fof(f33,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X2,X3),X2) | ~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f20])).
% 0.18/0.45  fof(f20,plain,(
% 0.18/0.45    ! [X0,X1,X2,X3] : ((k3_mcart_1(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)) = X0 & r2_hidden(sK9(X0,X1,X2,X3),X3) & r2_hidden(sK8(X0,X1,X2,X3),X2) & r2_hidden(sK7(X0,X1,X2,X3),X1)) | ~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f14,f19])).
% 0.18/0.45  fof(f19,plain,(
% 0.18/0.45    ! [X3,X2,X1,X0] : (? [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k3_mcart_1(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)) = X0 & r2_hidden(sK9(X0,X1,X2,X3),X3) & r2_hidden(sK8(X0,X1,X2,X3),X2) & r2_hidden(sK7(X0,X1,X2,X3),X1)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f14,plain,(
% 0.18/0.45    ! [X0,X1,X2,X3] : (? [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.18/0.45    inference(ennf_transformation,[],[f7])).
% 0.18/0.45  fof(f7,axiom,(
% 0.18/0.45    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.18/0.45  fof(f148,plain,(
% 0.18/0.45    ~r2_hidden(sK8(k1_mcart_1(sK0),sK1,sK2,sK3),sK2) | spl10_14),
% 0.18/0.45    inference(avatar_component_clause,[],[f146])).
% 0.18/0.45  fof(f146,plain,(
% 0.18/0.45    spl10_14 <=> r2_hidden(sK8(k1_mcart_1(sK0),sK1,sK2,sK3),sK2)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.18/0.45  fof(f176,plain,(
% 0.18/0.45    spl10_13),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f175])).
% 0.18/0.45  fof(f175,plain,(
% 0.18/0.45    $false | spl10_13),
% 0.18/0.45    inference(subsumption_resolution,[],[f174,f44])).
% 0.18/0.45  fof(f174,plain,(
% 0.18/0.45    ~r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | spl10_13),
% 0.18/0.45    inference(resolution,[],[f144,f41])).
% 0.18/0.45  fof(f41,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X2,X3),X1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.18/0.45    inference(definition_unfolding,[],[f32,f25])).
% 0.18/0.45  fof(f32,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X2,X3),X1) | ~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f20])).
% 0.18/0.45  fof(f144,plain,(
% 0.18/0.45    ~r2_hidden(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK1) | spl10_13),
% 0.18/0.45    inference(avatar_component_clause,[],[f142])).
% 0.18/0.45  fof(f142,plain,(
% 0.18/0.45    spl10_13 <=> r2_hidden(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK1)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.18/0.45  fof(f172,plain,(
% 0.18/0.45    spl10_15),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f171])).
% 0.18/0.45  fof(f171,plain,(
% 0.18/0.45    $false | spl10_15),
% 0.18/0.45    inference(subsumption_resolution,[],[f170,f69])).
% 0.18/0.45  fof(f69,plain,(
% 0.18/0.45    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)),
% 0.18/0.45    inference(resolution,[],[f44,f28])).
% 0.18/0.45  fof(f170,plain,(
% 0.18/0.45    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) | spl10_15),
% 0.18/0.45    inference(forward_demodulation,[],[f152,f140])).
% 0.18/0.45  fof(f140,plain,(
% 0.18/0.45    sK9(k1_mcart_1(sK0),sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK0))),
% 0.18/0.45    inference(superposition,[],[f24,f66])).
% 0.18/0.45  fof(f66,plain,(
% 0.18/0.45    k1_mcart_1(sK0) = k4_tarski(k4_tarski(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK8(k1_mcart_1(sK0),sK1,sK2,sK3)),sK9(k1_mcart_1(sK0),sK1,sK2,sK3))),
% 0.18/0.45    inference(resolution,[],[f44,f38])).
% 0.18/0.45  fof(f38,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) | k4_tarski(k4_tarski(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3)),sK9(X0,X1,X2,X3)) = X0) )),
% 0.18/0.45    inference(definition_unfolding,[],[f35,f26,f25])).
% 0.18/0.45  fof(f26,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f2])).
% 0.18/0.45  fof(f2,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.18/0.45  fof(f35,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)) = X0 | ~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f20])).
% 0.18/0.45  fof(f152,plain,(
% 0.18/0.45    ~r2_hidden(sK9(k1_mcart_1(sK0),sK1,sK2,sK3),sK3) | spl10_15),
% 0.18/0.45    inference(avatar_component_clause,[],[f150])).
% 0.18/0.45  fof(f150,plain,(
% 0.18/0.45    spl10_15 <=> r2_hidden(sK9(k1_mcart_1(sK0),sK1,sK2,sK3),sK3)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.18/0.45  fof(f156,plain,(
% 0.18/0.45    ~spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16),
% 0.18/0.45    inference(avatar_split_clause,[],[f137,f154,f150,f146,f142])).
% 0.18/0.45  fof(f137,plain,(
% 0.18/0.45    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK4) | ~r2_hidden(sK9(k1_mcart_1(sK0),sK1,sK2,sK3),sK3) | ~r2_hidden(sK8(k1_mcart_1(sK0),sK1,sK2,sK3),sK2) | ~r2_hidden(sK7(k1_mcart_1(sK0),sK1,sK2,sK3),sK1)) )),
% 0.18/0.45    inference(superposition,[],[f36,f66])).
% 0.18/0.45  fof(f36,plain,(
% 0.18/0.45    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.18/0.45    inference(definition_unfolding,[],[f22,f31])).
% 0.18/0.45  fof(f31,plain,(
% 0.18/0.45    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f5])).
% 0.18/0.45  fof(f5,axiom,(
% 0.18/0.45    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.18/0.45  fof(f22,plain,(
% 0.18/0.45    ( ! [X6,X8,X7,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  % SZS output end Proof for theBenchmark
% 0.18/0.45  % (9471)------------------------------
% 0.18/0.45  % (9471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (9471)Termination reason: Refutation
% 0.18/0.45  
% 0.18/0.45  % (9471)Memory used [KB]: 10746
% 0.18/0.45  % (9471)Time elapsed: 0.059 s
% 0.18/0.45  % (9471)------------------------------
% 0.18/0.45  % (9471)------------------------------
% 0.18/0.45  % (9462)Success in time 0.121 s
%------------------------------------------------------------------------------
