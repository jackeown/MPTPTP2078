%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:50 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 200 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  224 ( 869 expanded)
%              Number of equality atoms :   44 ( 173 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f325,f327,f329])).

fof(f329,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl10_2 ),
    inference(resolution,[],[f324,f69])).

fof(f69,plain,(
    r2_hidden(sK9(sK3,sK2,sK4),sK3) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    r2_hidden(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f55,plain,(
    r1_tarski(k2_tarski(sK4,sK4),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    r1_tarski(k2_tarski(sK4,sK4),sK1) ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK4
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    & r2_hidden(sK4,sK1)
    & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK4
          | ~ r2_hidden(X5,sK3)
          | ~ r2_hidden(X4,sK2) )
      & r2_hidden(sK4,sK1)
      & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k2_tarski(X0,sK4),sK1) ) ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f44,f43])).

% (5938)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(sK9(X2,X1,X0),X2) ) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X8,X2)
      | r2_hidden(sK9(X0,X1,X8),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X0)
                & r2_hidden(sK8(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (5934)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X0)
        & r2_hidden(sK6(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X0)
        & r2_hidden(sK8(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f324,plain,
    ( ~ r2_hidden(sK9(sK3,sK2,sK4),sK3)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl10_2
  <=> r2_hidden(sK9(sK3,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f327,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl10_1 ),
    inference(resolution,[],[f320,f62])).

% (5937)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f62,plain,(
    r2_hidden(sK8(sK3,sK2,sK4),sK2) ),
    inference(resolution,[],[f60,f56])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(sK8(X2,X1,X0),X1) ) ),
    inference(resolution,[],[f30,f46])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X8,X2)
      | r2_hidden(sK8(X0,X1,X8),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f320,plain,
    ( ~ r2_hidden(sK8(sK3,sK2,sK4),sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl10_1
  <=> r2_hidden(sK8(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f325,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f316,f322,f318])).

fof(f316,plain,
    ( ~ r2_hidden(sK9(sK3,sK2,sK4),sK3)
    | ~ r2_hidden(sK8(sK3,sK2,sK4),sK2) ),
    inference(trivial_inequality_removal,[],[f315])).

fof(f315,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK9(sK3,sK2,sK4),sK3)
    | ~ r2_hidden(sK8(sK3,sK2,sK4),sK2) ),
    inference(superposition,[],[f26,f201])).

fof(f201,plain,(
    sK4 = k4_tarski(sK8(sK3,sK2,sK4),sK9(sK3,sK2,sK4)) ),
    inference(resolution,[],[f122,f56])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK8(X2,X1,X0),sK9(X2,X1,X0)) = X0 ) ),
    inference(resolution,[],[f32,f46])).

fof(f32,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X8,X2)
      | k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK4
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (5945)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (5958)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.51  % (5950)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (5950)Refutation not found, incomplete strategy% (5950)------------------------------
% 0.19/0.52  % (5950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (5933)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.52  % (5948)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.52  % (5940)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.53  % (5935)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (5955)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (5950)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (5950)Memory used [KB]: 10618
% 1.28/0.53  % (5950)Time elapsed: 0.116 s
% 1.28/0.53  % (5950)------------------------------
% 1.28/0.53  % (5950)------------------------------
% 1.28/0.53  % (5945)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f330,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f325,f327,f329])).
% 1.28/0.53  fof(f329,plain,(
% 1.28/0.53    spl10_2),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f328])).
% 1.28/0.53  fof(f328,plain,(
% 1.28/0.53    $false | spl10_2),
% 1.28/0.53    inference(resolution,[],[f324,f69])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    r2_hidden(sK9(sK3,sK2,sK4),sK3)),
% 1.28/0.53    inference(resolution,[],[f68,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    r2_hidden(sK4,k2_zfmisc_1(sK2,sK3))),
% 1.28/0.53    inference(resolution,[],[f55,f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.28/0.53    inference(flattening,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.28/0.53    inference(nnf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    r1_tarski(k2_tarski(sK4,sK4),k2_zfmisc_1(sK2,sK3))),
% 1.28/0.53    inference(resolution,[],[f53,f50])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    r1_tarski(k2_tarski(sK4,sK4),sK1)),
% 1.28/0.53    inference(resolution,[],[f49,f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    r2_hidden(sK4,sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ! [X4,X5] : (k4_tarski(X4,X5) != sK4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) & r2_hidden(sK4,sK1) & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f8,f13])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2))) => (! [X5,X4] : (k4_tarski(X4,X5) != sK4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) & r2_hidden(sK4,sK1) & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f8,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.53    inference(ennf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.53    inference(negated_conjecture,[],[f6])).
% 1.28/0.53  fof(f6,conjecture,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_tarski(X0,sK4),sK1)) )),
% 1.28/0.53    inference(resolution,[],[f42,f25])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,k2_zfmisc_1(sK2,sK3))) )),
% 1.28/0.53    inference(resolution,[],[f48,f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    r1_tarski(sK1,k2_zfmisc_1(sK2,sK3))),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(superposition,[],[f44,f43])).
% 1.28/0.53  % (5938)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f28,f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,plain,(
% 1.28/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f29,f27])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.28/0.53    inference(ennf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.28/0.53  fof(f68,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK9(X2,X1,X0),X2)) )),
% 1.28/0.53    inference(resolution,[],[f31,f46])).
% 1.28/0.53  fof(f46,plain,(
% 1.28/0.53    ( ! [X0,X1] : (sP0(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.53    inference(equality_resolution,[],[f38])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f21])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(nnf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.28/0.53    inference(definition_folding,[],[f3,f11])).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.28/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X8,X2) | r2_hidden(sK9(X0,X1,X8),X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X0) & r2_hidden(sK8(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f16,f19,f18,f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  % (5934)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X0) & r2_hidden(sK8(X0,X1,X8),X1)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 1.28/0.53    inference(rectify,[],[f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.28/0.53    inference(nnf_transformation,[],[f11])).
% 1.28/0.53  fof(f324,plain,(
% 1.28/0.53    ~r2_hidden(sK9(sK3,sK2,sK4),sK3) | spl10_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f322])).
% 1.28/0.53  fof(f322,plain,(
% 1.28/0.53    spl10_2 <=> r2_hidden(sK9(sK3,sK2,sK4),sK3)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.28/0.53  fof(f327,plain,(
% 1.28/0.53    spl10_1),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f326])).
% 1.28/0.53  fof(f326,plain,(
% 1.28/0.53    $false | spl10_1),
% 1.28/0.53    inference(resolution,[],[f320,f62])).
% 1.28/0.53  % (5937)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.53  fof(f62,plain,(
% 1.28/0.53    r2_hidden(sK8(sK3,sK2,sK4),sK2)),
% 1.28/0.53    inference(resolution,[],[f60,f56])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK8(X2,X1,X0),X1)) )),
% 1.28/0.53    inference(resolution,[],[f30,f46])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X8,X2) | r2_hidden(sK8(X0,X1,X8),X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f320,plain,(
% 1.28/0.53    ~r2_hidden(sK8(sK3,sK2,sK4),sK2) | spl10_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f318])).
% 1.28/0.53  fof(f318,plain,(
% 1.28/0.53    spl10_1 <=> r2_hidden(sK8(sK3,sK2,sK4),sK2)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.28/0.53  fof(f325,plain,(
% 1.28/0.53    ~spl10_1 | ~spl10_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f316,f322,f318])).
% 1.28/0.53  fof(f316,plain,(
% 1.28/0.53    ~r2_hidden(sK9(sK3,sK2,sK4),sK3) | ~r2_hidden(sK8(sK3,sK2,sK4),sK2)),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f315])).
% 1.28/0.53  fof(f315,plain,(
% 1.28/0.53    sK4 != sK4 | ~r2_hidden(sK9(sK3,sK2,sK4),sK3) | ~r2_hidden(sK8(sK3,sK2,sK4),sK2)),
% 1.28/0.53    inference(superposition,[],[f26,f201])).
% 1.28/0.53  fof(f201,plain,(
% 1.28/0.53    sK4 = k4_tarski(sK8(sK3,sK2,sK4),sK9(sK3,sK2,sK4))),
% 1.28/0.53    inference(resolution,[],[f122,f56])).
% 1.28/0.53  fof(f122,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK8(X2,X1,X0),sK9(X2,X1,X0)) = X0) )),
% 1.28/0.53    inference(resolution,[],[f32,f46])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X8,X2) | k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (5945)------------------------------
% 1.28/0.53  % (5945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (5945)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (5945)Memory used [KB]: 6396
% 1.28/0.53  % (5956)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.53  % (5945)Time elapsed: 0.114 s
% 1.28/0.53  % (5945)------------------------------
% 1.28/0.53  % (5945)------------------------------
% 1.28/0.53  % (5936)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (5932)Success in time 0.179 s
%------------------------------------------------------------------------------
