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
% DateTime   : Thu Dec  3 12:58:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 294 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  275 (1395 expanded)
%              Number of equality atoms :   51 ( 252 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f603,f1255])).

fof(f1255,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f1254])).

fof(f1254,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f1246,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

% (10668)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f14,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f1246,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_1 ),
    inference(resolution,[],[f1230,f963])).

fof(f963,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(condensation,[],[f962])).

fof(f962,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f961,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f961,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(resolution,[],[f941,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f941,plain,
    ( ! [X19,X18] :
        ( ~ r1_tarski(X19,sK7(X19))
        | r1_xboole_0(X18,X19) )
    | ~ spl8_1 ),
    inference(resolution,[],[f913,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f913,plain,
    ( ! [X26,X25] :
        ( r1_xboole_0(X25,X26)
        | r2_hidden(sK7(X26),X26) )
    | ~ spl8_1 ),
    inference(resolution,[],[f668,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f23])).

fof(f23,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f668,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X2,X1)
        | r2_hidden(sK2(sK0,X0,X1),X1) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f663,f62])).

fof(f62,plain,
    ( ! [X16] : ~ r2_hidden(X16,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_1
  <=> ! [X16] : ~ r2_hidden(X16,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f663,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X2,X1)
        | r2_hidden(sK3(sK0,X0,X1),sK0)
        | r2_hidden(sK2(sK0,X0,X1),X1) )
    | ~ spl8_1 ),
    inference(superposition,[],[f626,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f18,f21,f20,f19])).

fof(f19,plain,(
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
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f626,plain,
    ( ! [X4,X3] : r1_xboole_0(X3,k2_zfmisc_1(sK0,X4))
    | ~ spl8_1 ),
    inference(resolution,[],[f616,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f616,plain,
    ( ! [X12,X13] : ~ r2_hidden(X12,k2_zfmisc_1(sK0,X13))
    | ~ spl8_1 ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1230,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK2(sK0,X8,X9),X9)
        | sK0 = X9 )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f1229,f1058])).

fof(f1058,plain,
    ( ! [X66] : sK0 = k2_zfmisc_1(sK0,X66)
    | ~ spl8_1 ),
    inference(resolution,[],[f1019,f62])).

fof(f1019,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,sK0),X2)
        | sK0 = k2_zfmisc_1(X2,X3) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f81,f62])).

fof(f81,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK1(sK2(X2,X3,sK0),sK0),sK0)
      | sK0 = k2_zfmisc_1(X2,X3)
      | r2_hidden(sK3(X2,X3,sK0),X2) ) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK1(X1,sK0),sK0) ) ),
    inference(resolution,[],[f26,f28])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1229,plain,
    ( ! [X8,X9] :
        ( k2_zfmisc_1(sK0,X8) = X9
        | r2_hidden(sK2(sK0,X8,X9),X9) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f84,f62])).

fof(f84,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1(sK3(sK0,X8,X9),sK0),sK0)
      | k2_zfmisc_1(sK0,X8) = X9
      | r2_hidden(sK2(sK0,X8,X9),X9) ) ),
    inference(resolution,[],[f49,f34])).

fof(f603,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f601,f25])).

fof(f601,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_2 ),
    inference(resolution,[],[f589,f41])).

fof(f589,plain,
    ( ! [X13] :
        ( ~ r1_tarski(X13,sK7(X13))
        | sK0 = X13 )
    | ~ spl8_2 ),
    inference(resolution,[],[f571,f40])).

fof(f571,plain,
    ( ! [X20] :
        ( r2_hidden(sK7(X20),X20)
        | sK0 = X20 )
    | ~ spl8_2 ),
    inference(resolution,[],[f565,f38])).

% (10668)Refutation not found, incomplete strategy% (10668)------------------------------
% (10668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10668)Termination reason: Refutation not found, incomplete strategy

% (10668)Memory used [KB]: 10618
% (10668)Time elapsed: 0.094 s
% (10668)------------------------------
% (10668)------------------------------
fof(f565,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK2(sK0,X8,X9),X9)
        | sK0 = X9 )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f564,f419])).

fof(f419,plain,
    ( ! [X58] : sK0 = k2_zfmisc_1(sK0,X58)
    | ~ spl8_2 ),
    inference(resolution,[],[f374,f89])).

fof(f89,plain,
    ( ! [X16] : ~ r2_hidden(X16,sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f88,f68])).

fof(f68,plain,
    ( ~ r2_hidden(sK1(sK7(sK0),sK0),sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK7(X1)) ) ),
    inference(condensation,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK7(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,
    ( r2_hidden(sK1(sK7(sK0),sK0),sK7(sK0))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl8_2
  <=> r2_hidden(sK1(sK7(sK0),sK0),sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f88,plain,(
    ! [X16] :
      ( r2_hidden(sK1(sK7(sK0),sK0),sK0)
      | ~ r2_hidden(X16,sK0) ) ),
    inference(resolution,[],[f49,f38])).

fof(f374,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,sK0),X2)
        | sK0 = k2_zfmisc_1(X2,X3) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f81,f89])).

fof(f564,plain,
    ( ! [X8,X9] :
        ( k2_zfmisc_1(sK0,X8) = X9
        | r2_hidden(sK2(sK0,X8,X9),X9) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f84,f89])).

fof(f67,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f59,f64,f61])).

fof(f59,plain,(
    ! [X16] :
      ( r2_hidden(sK1(sK7(sK0),sK0),sK7(sK0))
      | ~ r2_hidden(X16,sK0) ) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK1(X0,sK0),X0) ) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (10687)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (10687)Refutation not found, incomplete strategy% (10687)------------------------------
% 0.21/0.46  % (10687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10687)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (10687)Memory used [KB]: 10618
% 0.21/0.46  % (10687)Time elapsed: 0.045 s
% 0.21/0.46  % (10687)------------------------------
% 0.21/0.46  % (10687)------------------------------
% 0.21/0.47  % (10671)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (10686)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (10678)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (10678)Refutation not found, incomplete strategy% (10678)------------------------------
% 0.21/0.48  % (10678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10678)Memory used [KB]: 10618
% 0.21/0.48  % (10678)Time elapsed: 0.058 s
% 0.21/0.48  % (10678)------------------------------
% 0.21/0.48  % (10678)------------------------------
% 0.21/0.48  % (10667)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (10681)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (10672)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (10680)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (10669)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (10670)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (10682)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (10682)Refutation not found, incomplete strategy% (10682)------------------------------
% 0.21/0.49  % (10682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10682)Memory used [KB]: 6140
% 0.21/0.49  % (10682)Time elapsed: 0.084 s
% 0.21/0.49  % (10682)------------------------------
% 0.21/0.49  % (10682)------------------------------
% 0.21/0.50  % (10667)Refutation not found, incomplete strategy% (10667)------------------------------
% 0.21/0.50  % (10667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10667)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10667)Memory used [KB]: 6140
% 0.21/0.50  % (10667)Time elapsed: 0.066 s
% 0.21/0.50  % (10667)------------------------------
% 0.21/0.50  % (10667)------------------------------
% 0.21/0.50  % (10676)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (10677)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (10673)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (10674)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (10670)Refutation not found, incomplete strategy% (10670)------------------------------
% 0.21/0.50  % (10670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10670)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10670)Memory used [KB]: 10618
% 0.21/0.50  % (10670)Time elapsed: 0.085 s
% 0.21/0.50  % (10670)------------------------------
% 0.21/0.50  % (10670)------------------------------
% 0.21/0.50  % (10683)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (10677)Refutation not found, incomplete strategy% (10677)------------------------------
% 0.21/0.50  % (10677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10677)Memory used [KB]: 6140
% 0.21/0.50  % (10677)Time elapsed: 0.092 s
% 0.21/0.50  % (10677)------------------------------
% 0.21/0.50  % (10677)------------------------------
% 0.21/0.50  % (10684)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (10686)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1256,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f67,f603,f1255])).
% 0.21/0.50  fof(f1255,plain,(
% 0.21/0.50    ~spl8_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1254])).
% 0.21/0.50  fof(f1254,plain,(
% 0.21/0.50    $false | ~spl8_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f1246,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % (10668)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.51  fof(f1246,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f1230,f963])).
% 0.21/0.51  fof(f963,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_1),
% 0.21/0.51    inference(condensation,[],[f962])).
% 0.21/0.51  fof(f962,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f961,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f961,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f941,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f941,plain,(
% 0.21/0.51    ( ! [X19,X18] : (~r1_tarski(X19,sK7(X19)) | r1_xboole_0(X18,X19)) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f913,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f913,plain,(
% 0.21/0.51    ( ! [X26,X25] : (r1_xboole_0(X25,X26) | r2_hidden(sK7(X26),X26)) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f668,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.51  fof(f668,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X2,X1) | r2_hidden(sK2(sK0,X0,X1),X1)) ) | ~spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f663,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X16] : (~r2_hidden(X16,sK0)) ) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl8_1 <=> ! [X16] : ~r2_hidden(X16,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f663,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X2,X1) | r2_hidden(sK3(sK0,X0,X1),sK0) | r2_hidden(sK2(sK0,X0,X1),X1)) ) | ~spl8_1),
% 0.21/0.51    inference(superposition,[],[f626,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f18,f21,f20,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.51    inference(rectify,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.51  fof(f626,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r1_xboole_0(X3,k2_zfmisc_1(sK0,X4))) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f616,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f616,plain,(
% 0.21/0.51    ( ! [X12,X13] : (~r2_hidden(X12,k2_zfmisc_1(sK0,X13))) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f62,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f1230,plain,(
% 0.21/0.51    ( ! [X8,X9] : (r2_hidden(sK2(sK0,X8,X9),X9) | sK0 = X9) ) | ~spl8_1),
% 0.21/0.51    inference(forward_demodulation,[],[f1229,f1058])).
% 0.21/0.51  fof(f1058,plain,(
% 0.21/0.51    ( ! [X66] : (sK0 = k2_zfmisc_1(sK0,X66)) ) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f1019,f62])).
% 0.21/0.51  fof(f1019,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,sK0),X2) | sK0 = k2_zfmisc_1(X2,X3)) ) | ~spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f62])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK1(sK2(X2,X3,sK0),sK0),sK0) | sK0 = k2_zfmisc_1(X2,X3) | r2_hidden(sK3(X2,X3,sK0),X2)) )),
% 0.21/0.51    inference(resolution,[],[f49,f34])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(sK1(X1,sK0),sK0)) )),
% 0.21/0.51    inference(resolution,[],[f26,f28])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f1229,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k2_zfmisc_1(sK0,X8) = X9 | r2_hidden(sK2(sK0,X8,X9),X9)) ) | ~spl8_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f62])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X8,X9] : (r2_hidden(sK1(sK3(sK0,X8,X9),sK0),sK0) | k2_zfmisc_1(sK0,X8) = X9 | r2_hidden(sK2(sK0,X8,X9),X9)) )),
% 0.21/0.51    inference(resolution,[],[f49,f34])).
% 0.21/0.51  fof(f603,plain,(
% 0.21/0.51    ~spl8_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f602])).
% 0.21/0.51  fof(f602,plain,(
% 0.21/0.51    $false | ~spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f601,f25])).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f589,f41])).
% 0.21/0.51  fof(f589,plain,(
% 0.21/0.51    ( ! [X13] : (~r1_tarski(X13,sK7(X13)) | sK0 = X13) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f571,f40])).
% 0.21/0.51  fof(f571,plain,(
% 0.21/0.51    ( ! [X20] : (r2_hidden(sK7(X20),X20) | sK0 = X20) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f565,f38])).
% 0.21/0.51  % (10668)Refutation not found, incomplete strategy% (10668)------------------------------
% 0.21/0.51  % (10668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10668)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10668)Memory used [KB]: 10618
% 0.21/0.51  % (10668)Time elapsed: 0.094 s
% 0.21/0.51  % (10668)------------------------------
% 0.21/0.51  % (10668)------------------------------
% 0.21/0.51  fof(f565,plain,(
% 0.21/0.51    ( ! [X8,X9] : (r2_hidden(sK2(sK0,X8,X9),X9) | sK0 = X9) ) | ~spl8_2),
% 0.21/0.51    inference(forward_demodulation,[],[f564,f419])).
% 0.21/0.51  fof(f419,plain,(
% 0.21/0.51    ( ! [X58] : (sK0 = k2_zfmisc_1(sK0,X58)) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f374,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X16] : (~r2_hidden(X16,sK0)) ) | ~spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~r2_hidden(sK1(sK7(sK0),sK0),sK0) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f66,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,sK7(X1))) )),
% 0.21/0.51    inference(condensation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    r2_hidden(sK1(sK7(sK0),sK0),sK7(sK0)) | ~spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl8_2 <=> r2_hidden(sK1(sK7(sK0),sK0),sK7(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X16] : (r2_hidden(sK1(sK7(sK0),sK0),sK0) | ~r2_hidden(X16,sK0)) )),
% 0.21/0.51    inference(resolution,[],[f49,f38])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,sK0),X2) | sK0 = k2_zfmisc_1(X2,X3)) ) | ~spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f89])).
% 0.21/0.51  fof(f564,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k2_zfmisc_1(sK0,X8) = X9 | r2_hidden(sK2(sK0,X8,X9),X9)) ) | ~spl8_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f89])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl8_1 | spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f59,f64,f61])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X16] : (r2_hidden(sK1(sK7(sK0),sK0),sK7(sK0)) | ~r2_hidden(X16,sK0)) )),
% 0.21/0.51    inference(resolution,[],[f48,f38])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(X0,sK0),X0)) )),
% 0.21/0.51    inference(resolution,[],[f26,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (10686)------------------------------
% 0.21/0.51  % (10686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10686)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (10686)Memory used [KB]: 6652
% 0.21/0.51  % (10686)Time elapsed: 0.086 s
% 0.21/0.51  % (10686)------------------------------
% 0.21/0.51  % (10686)------------------------------
% 0.21/0.51  % (10666)Success in time 0.149 s
%------------------------------------------------------------------------------
