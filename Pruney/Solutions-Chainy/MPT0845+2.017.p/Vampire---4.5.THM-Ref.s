%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 116 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  220 ( 490 expanded)
%              Number of equality atoms :   47 ( 103 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f447,f509])).

fof(f509,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f486,f51])).

fof(f51,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_1
  <=> r1_xboole_0(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f486,plain,
    ( ! [X6] : r1_xboole_0(X6,sK0)
    | spl8_1 ),
    inference(resolution,[],[f477,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f477,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | spl8_1 ),
    inference(resolution,[],[f117,f51])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_xboole_0(sK2(X1),X1)
      | r1_xboole_0(sK2(X1),X1) ) ),
    inference(resolution,[],[f65,f29])).

fof(f65,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK1(sK2(X3),X4),X3)
      | ~ r2_hidden(X5,X3)
      | r1_xboole_0(sK2(X3),X4) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f447,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl8_2 ),
    inference(resolution,[],[f330,f370])).

fof(f370,plain,
    ( ! [X7] : r1_xboole_0(X7,sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f29,f54])).

fof(f54,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_2
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f330,plain,(
    ! [X18] : ~ r1_xboole_0(sK3(k1_xboole_0,X18,sK0),sK0) ),
    inference(subsumption_resolution,[],[f329,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f329,plain,(
    ! [X18] :
      ( k1_xboole_0 = sK0
      | ~ r1_xboole_0(sK3(k1_xboole_0,X18,sK0),sK0) ) ),
    inference(forward_demodulation,[],[f215,f209])).

fof(f209,plain,(
    ! [X6] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X6) ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f81,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(k1_xboole_0,X4,X5),X5)
      | k2_zfmisc_1(k1_xboole_0,X4) = X5 ) ),
    inference(resolution,[],[f39,f62])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
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
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f215,plain,(
    ! [X18] :
      ( sK0 = k2_zfmisc_1(k1_xboole_0,X18)
      | ~ r1_xboole_0(sK3(k1_xboole_0,X18,sK0),sK0) ) ),
    inference(resolution,[],[f81,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f48,f53,f50])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_xboole_0(sK2(sK0),sK0) ) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (7966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (7976)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (7975)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (7976)Refutation not found, incomplete strategy% (7976)------------------------------
% 0.21/0.49  % (7976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7968)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (7976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7976)Memory used [KB]: 6140
% 0.21/0.49  % (7976)Time elapsed: 0.008 s
% 0.21/0.49  % (7976)------------------------------
% 0.21/0.49  % (7976)------------------------------
% 0.21/0.50  % (7981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (7981)Refutation not found, incomplete strategy% (7981)------------------------------
% 0.21/0.50  % (7981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7981)Memory used [KB]: 10618
% 0.21/0.50  % (7981)Time elapsed: 0.074 s
% 0.21/0.50  % (7981)------------------------------
% 0.21/0.50  % (7981)------------------------------
% 0.21/0.50  % (7963)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (7973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7967)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (7971)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (7970)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (7971)Refutation not found, incomplete strategy% (7971)------------------------------
% 0.21/0.52  % (7971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7971)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7971)Memory used [KB]: 6140
% 0.21/0.52  % (7971)Time elapsed: 0.100 s
% 0.21/0.52  % (7971)------------------------------
% 0.21/0.52  % (7971)------------------------------
% 0.21/0.53  % (7974)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.53  % (7980)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (7961)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7961)Refutation not found, incomplete strategy% (7961)------------------------------
% 0.21/0.54  % (7961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7961)Memory used [KB]: 6140
% 0.21/0.54  % (7961)Time elapsed: 0.104 s
% 0.21/0.54  % (7961)------------------------------
% 0.21/0.54  % (7961)------------------------------
% 0.21/0.54  % (7963)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (7964)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (7962)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (7965)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (7962)Refutation not found, incomplete strategy% (7962)------------------------------
% 0.21/0.54  % (7962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7962)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7962)Memory used [KB]: 10618
% 0.21/0.54  % (7962)Time elapsed: 0.114 s
% 0.21/0.54  % (7962)------------------------------
% 0.21/0.54  % (7962)------------------------------
% 0.21/0.54  % (7972)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.54  % (7969)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.54  % (7972)Refutation not found, incomplete strategy% (7972)------------------------------
% 0.21/0.54  % (7972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7972)Memory used [KB]: 10618
% 0.21/0.54  % (7972)Time elapsed: 0.120 s
% 0.21/0.54  % (7972)------------------------------
% 0.21/0.54  % (7972)------------------------------
% 0.21/0.55  % (7977)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.55  % (7964)Refutation not found, incomplete strategy% (7964)------------------------------
% 0.21/0.55  % (7964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7964)Memory used [KB]: 10618
% 0.21/0.55  % (7964)Time elapsed: 0.113 s
% 0.21/0.55  % (7964)------------------------------
% 0.21/0.55  % (7964)------------------------------
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f510,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f55,f447,f509])).
% 1.46/0.55  fof(f509,plain,(
% 1.46/0.55    spl8_1),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f499])).
% 1.46/0.55  fof(f499,plain,(
% 1.46/0.55    $false | spl8_1),
% 1.46/0.55    inference(resolution,[],[f486,f51])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ~r1_xboole_0(sK2(sK0),sK0) | spl8_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    spl8_1 <=> r1_xboole_0(sK2(sK0),sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.46/0.56  fof(f486,plain,(
% 1.46/0.56    ( ! [X6] : (r1_xboole_0(X6,sK0)) ) | spl8_1),
% 1.46/0.56    inference(resolution,[],[f477,f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f15])).
% 1.46/0.56  fof(f15,plain,(
% 1.46/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).
% 1.46/0.56  fof(f14,plain,(
% 1.46/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f10,plain,(
% 1.46/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,plain,(
% 1.46/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.46/0.56    inference(rectify,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.46/0.56  fof(f477,plain,(
% 1.46/0.56    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | spl8_1),
% 1.46/0.56    inference(resolution,[],[f117,f51])).
% 1.46/0.56  fof(f117,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_xboole_0(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f116])).
% 1.46/0.56  fof(f116,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_xboole_0(sK2(X1),X1) | r1_xboole_0(sK2(X1),X1)) )),
% 1.46/0.56    inference(resolution,[],[f65,f29])).
% 1.46/0.56  fof(f65,plain,(
% 1.46/0.56    ( ! [X4,X5,X3] : (~r2_hidden(sK1(sK2(X3),X4),X3) | ~r2_hidden(X5,X3) | r1_xboole_0(sK2(X3),X4)) )),
% 1.46/0.56    inference(resolution,[],[f34,f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f15])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,plain,(
% 1.46/0.56    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 1.46/0.56  fof(f17,plain,(
% 1.46/0.56    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f11,plain,(
% 1.46/0.56    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 1.46/0.56  fof(f447,plain,(
% 1.46/0.56    ~spl8_2),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f446])).
% 1.46/0.56  fof(f446,plain,(
% 1.46/0.56    $false | ~spl8_2),
% 1.46/0.56    inference(resolution,[],[f330,f370])).
% 1.46/0.56  fof(f370,plain,(
% 1.46/0.56    ( ! [X7] : (r1_xboole_0(X7,sK0)) ) | ~spl8_2),
% 1.46/0.56    inference(resolution,[],[f29,f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f53])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    spl8_2 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.46/0.56  fof(f330,plain,(
% 1.46/0.56    ( ! [X18] : (~r1_xboole_0(sK3(k1_xboole_0,X18,sK0),sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f329,f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    k1_xboole_0 != sK0),
% 1.46/0.56    inference(cnf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,plain,(
% 1.46/0.56    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 1.46/0.56  fof(f12,plain,(
% 1.46/0.56    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f9,plain,(
% 1.46/0.56    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,negated_conjecture,(
% 1.46/0.56    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.46/0.56    inference(negated_conjecture,[],[f6])).
% 1.46/0.56  fof(f6,conjecture,(
% 1.46/0.56    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 1.46/0.56  fof(f329,plain,(
% 1.46/0.56    ( ! [X18] : (k1_xboole_0 = sK0 | ~r1_xboole_0(sK3(k1_xboole_0,X18,sK0),sK0)) )),
% 1.46/0.56    inference(forward_demodulation,[],[f215,f209])).
% 1.46/0.56  fof(f209,plain,(
% 1.46/0.56    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X6)) )),
% 1.46/0.56    inference(resolution,[],[f81,f62])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f61])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.46/0.56    inference(superposition,[],[f31,f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,plain,(
% 1.46/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.46/0.56  fof(f81,plain,(
% 1.46/0.56    ( ! [X4,X5] : (r2_hidden(sK3(k1_xboole_0,X4,X5),X5) | k2_zfmisc_1(k1_xboole_0,X4) = X5) )),
% 1.46/0.56    inference(resolution,[],[f39,f62])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.46/0.56    inference(rectify,[],[f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.46/0.56    inference(nnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.46/0.56  fof(f215,plain,(
% 1.46/0.56    ( ! [X18] : (sK0 = k2_zfmisc_1(k1_xboole_0,X18) | ~r1_xboole_0(sK3(k1_xboole_0,X18,sK0),sK0)) )),
% 1.46/0.56    inference(resolution,[],[f81,f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f13])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    ~spl8_1 | spl8_2),
% 1.46/0.56    inference(avatar_split_clause,[],[f48,f53,f50])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r1_xboole_0(sK2(sK0),sK0)) )),
% 1.46/0.56    inference(resolution,[],[f33,f26])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (7963)------------------------------
% 1.46/0.56  % (7963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (7963)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (7963)Memory used [KB]: 10874
% 1.46/0.56  % (7963)Time elapsed: 0.114 s
% 1.46/0.56  % (7963)------------------------------
% 1.46/0.56  % (7963)------------------------------
% 1.46/0.56  % (7978)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.46/0.56  % (7979)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.46/0.56  % (7960)Success in time 0.191 s
%------------------------------------------------------------------------------
