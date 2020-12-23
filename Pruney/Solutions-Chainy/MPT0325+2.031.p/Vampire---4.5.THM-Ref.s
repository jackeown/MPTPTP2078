%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 179 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 ( 715 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17263)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f399,f443,f478,f518,f529,f538])).

fof(f538,plain,
    ( ~ spl13_15
    | spl13_1 ),
    inference(avatar_split_clause,[],[f100,f90,f515])).

fof(f515,plain,
    ( spl13_15
  <=> r2_hidden(sK5(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f90,plain,
    ( spl13_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f100,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK2)
    | spl13_1 ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f92,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f529,plain,
    ( ~ spl13_14
    | spl13_2 ),
    inference(avatar_split_clause,[],[f103,f94,f475])).

fof(f475,plain,
    ( spl13_14
  <=> r2_hidden(sK5(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f94,plain,
    ( spl13_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f103,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | spl13_2 ),
    inference(resolution,[],[f96,f45])).

fof(f96,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f518,plain,
    ( spl13_15
    | spl13_10
    | spl13_1 ),
    inference(avatar_split_clause,[],[f501,f90,f370,f515])).

fof(f370,plain,
    ( spl13_10
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f501,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(sK5(sK0,sK2),sK2) )
    | spl13_1 ),
    inference(resolution,[],[f225,f177])).

fof(f177,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f105,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f105,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f37,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f225,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(sK5(sK0,sK2),X1),k2_zfmisc_1(sK0,X2))
        | ~ r2_hidden(X1,X2) )
    | spl13_1 ),
    inference(resolution,[],[f99,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | spl13_1 ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f478,plain,
    ( spl13_14
    | spl13_12
    | spl13_2 ),
    inference(avatar_split_clause,[],[f461,f94,f402,f475])).

fof(f402,plain,
    ( spl13_12
  <=> ! [X3] : ~ r2_hidden(X3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f461,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | r2_hidden(sK5(sK1,sK3),sK3) )
    | spl13_2 ),
    inference(resolution,[],[f145,f178])).

fof(f178,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X5,sK3) ) ),
    inference(resolution,[],[f105,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f145,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k4_tarski(X3,sK5(sK1,sK3)),k2_zfmisc_1(X4,sK1))
        | ~ r2_hidden(X3,X4) )
    | spl13_2 ),
    inference(resolution,[],[f102,f64])).

fof(f102,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | spl13_2 ),
    inference(resolution,[],[f96,f44])).

fof(f443,plain,(
    ~ spl13_12 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl13_12 ),
    inference(resolution,[],[f403,f166])).

fof(f166,plain,(
    r2_hidden(sK10(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK0) ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
              & r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
                & r2_hidden(sK11(X0,X1,X8),X1)
                & r2_hidden(sK10(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f30,f33,f32,f31])).

fof(f31,plain,(
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
              ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
        & r2_hidden(sK11(X0,X1,X8),X1)
        & r2_hidden(sK10(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f104,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f74,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | sQ12_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f42,f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f74,plain,(
    ~ sQ12_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f38,f73])).

fof(f38,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f403,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f402])).

fof(f399,plain,(
    ~ spl13_10 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl13_10 ),
    inference(resolution,[],[f371,f167])).

fof(f167,plain,(
    r2_hidden(sK11(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1) ),
    inference(resolution,[],[f104,f71])).

fof(f71,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f371,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f370])).

fof(f97,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f39,f94,f90])).

fof(f39,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:14:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.46  % (17252)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.48  % (17269)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.49  % (17277)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (17251)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (17249)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (17272)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.50  % (17247)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (17267)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.50  % (17250)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (17270)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (17260)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (17261)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (17268)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (17258)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (17254)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (17270)Refutation not found, incomplete strategy% (17270)------------------------------
% 0.19/0.51  % (17270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (17270)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (17270)Memory used [KB]: 10746
% 0.19/0.51  % (17270)Time elapsed: 0.077 s
% 0.19/0.51  % (17270)------------------------------
% 0.19/0.51  % (17270)------------------------------
% 0.19/0.52  % (17259)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (17253)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (17248)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (17262)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (17271)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (17255)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.53  % (17276)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (17275)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (17274)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (17273)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (17268)Refutation not found, incomplete strategy% (17268)------------------------------
% 0.19/0.53  % (17268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (17268)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (17268)Memory used [KB]: 10746
% 0.19/0.53  % (17268)Time elapsed: 0.144 s
% 0.19/0.53  % (17268)------------------------------
% 0.19/0.53  % (17268)------------------------------
% 0.19/0.53  % (17266)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.54  % (17265)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.54  % (17257)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (17256)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  % (17262)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  % (17263)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.56  fof(f539,plain,(
% 1.59/0.56    $false),
% 1.59/0.56    inference(avatar_sat_refutation,[],[f97,f399,f443,f478,f518,f529,f538])).
% 1.59/0.56  fof(f538,plain,(
% 1.59/0.56    ~spl13_15 | spl13_1),
% 1.59/0.56    inference(avatar_split_clause,[],[f100,f90,f515])).
% 1.59/0.56  fof(f515,plain,(
% 1.59/0.56    spl13_15 <=> r2_hidden(sK5(sK0,sK2),sK2)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 1.59/0.56  fof(f90,plain,(
% 1.59/0.56    spl13_1 <=> r1_tarski(sK0,sK2)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.59/0.56  fof(f100,plain,(
% 1.59/0.56    ~r2_hidden(sK5(sK0,sK2),sK2) | spl13_1),
% 1.59/0.56    inference(resolution,[],[f92,f45])).
% 1.59/0.56  fof(f45,plain,(
% 1.59/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f22])).
% 1.59/0.56  fof(f22,plain,(
% 1.59/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 1.59/0.56  fof(f21,plain,(
% 1.59/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f20,plain,(
% 1.59/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.56    inference(rectify,[],[f19])).
% 1.59/0.56  fof(f19,plain,(
% 1.59/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.56    inference(nnf_transformation,[],[f14])).
% 1.59/0.56  fof(f14,plain,(
% 1.59/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.56    inference(ennf_transformation,[],[f1])).
% 1.59/0.56  fof(f1,axiom,(
% 1.59/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.56  fof(f92,plain,(
% 1.59/0.56    ~r1_tarski(sK0,sK2) | spl13_1),
% 1.59/0.56    inference(avatar_component_clause,[],[f90])).
% 1.59/0.56  fof(f529,plain,(
% 1.59/0.56    ~spl13_14 | spl13_2),
% 1.59/0.56    inference(avatar_split_clause,[],[f103,f94,f475])).
% 1.59/0.56  fof(f475,plain,(
% 1.59/0.56    spl13_14 <=> r2_hidden(sK5(sK1,sK3),sK3)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 1.59/0.56  fof(f94,plain,(
% 1.59/0.56    spl13_2 <=> r1_tarski(sK1,sK3)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.59/0.56  fof(f103,plain,(
% 1.59/0.56    ~r2_hidden(sK5(sK1,sK3),sK3) | spl13_2),
% 1.59/0.56    inference(resolution,[],[f96,f45])).
% 1.59/0.56  fof(f96,plain,(
% 1.59/0.56    ~r1_tarski(sK1,sK3) | spl13_2),
% 1.59/0.56    inference(avatar_component_clause,[],[f94])).
% 1.59/0.56  fof(f518,plain,(
% 1.59/0.56    spl13_15 | spl13_10 | spl13_1),
% 1.59/0.56    inference(avatar_split_clause,[],[f501,f90,f370,f515])).
% 1.59/0.56  fof(f370,plain,(
% 1.59/0.56    spl13_10 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.59/0.56  fof(f501,plain,(
% 1.59/0.56    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(sK5(sK0,sK2),sK2)) ) | spl13_1),
% 1.59/0.56    inference(resolution,[],[f225,f177])).
% 1.59/0.56  fof(f177,plain,(
% 1.59/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X2,sK2)) )),
% 1.59/0.56    inference(resolution,[],[f105,f62])).
% 1.59/0.56  fof(f62,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.59/0.56    inference(cnf_transformation,[],[f36])).
% 1.59/0.56  fof(f36,plain,(
% 1.59/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.59/0.56    inference(flattening,[],[f35])).
% 1.59/0.56  fof(f35,plain,(
% 1.59/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.59/0.56    inference(nnf_transformation,[],[f8])).
% 1.59/0.56  fof(f8,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.59/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.59/0.56  fof(f105,plain,(
% 1.59/0.56    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) )),
% 1.59/0.56    inference(resolution,[],[f37,f43])).
% 1.59/0.56  fof(f43,plain,(
% 1.59/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f22])).
% 1.59/0.56  fof(f37,plain,(
% 1.59/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.59/0.56    inference(cnf_transformation,[],[f16])).
% 1.59/0.56  fof(f16,plain,(
% 1.59/0.56    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).
% 1.59/0.56  fof(f15,plain,(
% 1.59/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f12,plain,(
% 1.59/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.59/0.56    inference(flattening,[],[f11])).
% 1.59/0.56  fof(f11,plain,(
% 1.59/0.56    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.59/0.56    inference(ennf_transformation,[],[f10])).
% 1.59/0.56  fof(f10,negated_conjecture,(
% 1.59/0.56    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.59/0.56    inference(negated_conjecture,[],[f9])).
% 1.59/0.56  fof(f9,conjecture,(
% 1.59/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.59/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.59/0.56  fof(f225,plain,(
% 1.59/0.56    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK5(sK0,sK2),X1),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X1,X2)) ) | spl13_1),
% 1.59/0.56    inference(resolution,[],[f99,f64])).
% 1.59/0.56  fof(f64,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f36])).
% 1.59/0.56  fof(f99,plain,(
% 1.59/0.56    r2_hidden(sK5(sK0,sK2),sK0) | spl13_1),
% 1.59/0.56    inference(resolution,[],[f92,f44])).
% 1.59/0.56  fof(f44,plain,(
% 1.59/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f22])).
% 1.59/0.56  fof(f478,plain,(
% 1.59/0.56    spl13_14 | spl13_12 | spl13_2),
% 1.59/0.56    inference(avatar_split_clause,[],[f461,f94,f402,f475])).
% 1.59/0.56  fof(f402,plain,(
% 1.59/0.56    spl13_12 <=> ! [X3] : ~r2_hidden(X3,sK0)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 1.59/0.56  fof(f461,plain,(
% 1.59/0.56    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(sK5(sK1,sK3),sK3)) ) | spl13_2),
% 1.59/0.56    inference(resolution,[],[f145,f178])).
% 1.59/0.56  fof(f178,plain,(
% 1.59/0.56    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X5,sK3)) )),
% 1.59/0.56    inference(resolution,[],[f105,f63])).
% 1.59/0.56  fof(f63,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.59/0.56    inference(cnf_transformation,[],[f36])).
% 1.59/0.56  fof(f145,plain,(
% 1.59/0.56    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK5(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | ~r2_hidden(X3,X4)) ) | spl13_2),
% 1.59/0.56    inference(resolution,[],[f102,f64])).
% 1.59/0.56  fof(f102,plain,(
% 1.59/0.56    r2_hidden(sK5(sK1,sK3),sK1) | spl13_2),
% 1.59/0.56    inference(resolution,[],[f96,f44])).
% 1.59/0.56  fof(f443,plain,(
% 1.59/0.56    ~spl13_12),
% 1.59/0.56    inference(avatar_contradiction_clause,[],[f429])).
% 1.59/0.56  fof(f429,plain,(
% 1.59/0.56    $false | ~spl13_12),
% 1.59/0.56    inference(resolution,[],[f403,f166])).
% 1.59/0.56  fof(f166,plain,(
% 1.59/0.56    r2_hidden(sK10(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK0)),
% 1.59/0.56    inference(resolution,[],[f104,f72])).
% 1.59/0.56  fof(f72,plain,(
% 1.59/0.56    ( ! [X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.59/0.56    inference(equality_resolution,[],[f54])).
% 1.59/0.56  fof(f54,plain,(
% 1.59/0.56    ( ! [X2,X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.59/0.56    inference(cnf_transformation,[],[f34])).
% 1.59/0.56  fof(f34,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f30,f33,f32,f31])).
% 1.59/0.56  fof(f31,plain,(
% 1.59/0.56    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f32,plain,(
% 1.59/0.56    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f33,plain,(
% 1.59/0.56    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f30,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.59/0.56    inference(rectify,[],[f29])).
% 1.59/0.56  fof(f29,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.59/0.56    inference(nnf_transformation,[],[f7])).
% 1.59/0.56  fof(f7,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.59/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.59/0.56  fof(f104,plain,(
% 1.59/0.56    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 1.59/0.56    inference(resolution,[],[f74,f77])).
% 1.59/0.56  fof(f77,plain,(
% 1.59/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | sQ12_eqProxy(k1_xboole_0,X0)) )),
% 1.59/0.56    inference(equality_proxy_replacement,[],[f42,f73])).
% 1.59/0.56  fof(f73,plain,(
% 1.59/0.56    ! [X1,X0] : (sQ12_eqProxy(X0,X1) <=> X0 = X1)),
% 1.59/0.56    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).
% 1.59/0.56  fof(f42,plain,(
% 1.59/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.59/0.56    inference(cnf_transformation,[],[f18])).
% 1.59/0.56  fof(f18,plain,(
% 1.59/0.56    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f17])).
% 1.59/0.56  fof(f17,plain,(
% 1.59/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f13,plain,(
% 1.59/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.59/0.56    inference(ennf_transformation,[],[f3])).
% 1.59/0.56  fof(f3,axiom,(
% 1.59/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.59/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.59/0.56  fof(f74,plain,(
% 1.59/0.56    ~sQ12_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 1.59/0.56    inference(equality_proxy_replacement,[],[f38,f73])).
% 1.59/0.56  fof(f38,plain,(
% 1.59/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.59/0.56    inference(cnf_transformation,[],[f16])).
% 1.59/0.56  fof(f403,plain,(
% 1.59/0.56    ( ! [X3] : (~r2_hidden(X3,sK0)) ) | ~spl13_12),
% 1.59/0.56    inference(avatar_component_clause,[],[f402])).
% 1.59/0.56  fof(f399,plain,(
% 1.59/0.56    ~spl13_10),
% 1.59/0.56    inference(avatar_contradiction_clause,[],[f385])).
% 1.59/0.56  fof(f385,plain,(
% 1.59/0.56    $false | ~spl13_10),
% 1.59/0.56    inference(resolution,[],[f371,f167])).
% 1.59/0.56  fof(f167,plain,(
% 1.59/0.56    r2_hidden(sK11(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1)),
% 1.59/0.56    inference(resolution,[],[f104,f71])).
% 1.59/0.56  fof(f71,plain,(
% 1.59/0.56    ( ! [X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.59/0.56    inference(equality_resolution,[],[f55])).
% 1.59/0.56  fof(f55,plain,(
% 1.59/0.56    ( ! [X2,X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.59/0.56    inference(cnf_transformation,[],[f34])).
% 1.59/0.56  fof(f371,plain,(
% 1.59/0.56    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl13_10),
% 1.59/0.56    inference(avatar_component_clause,[],[f370])).
% 1.59/0.56  fof(f97,plain,(
% 1.59/0.56    ~spl13_1 | ~spl13_2),
% 1.59/0.56    inference(avatar_split_clause,[],[f39,f94,f90])).
% 1.59/0.56  fof(f39,plain,(
% 1.59/0.56    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 1.59/0.56    inference(cnf_transformation,[],[f16])).
% 1.59/0.56  % SZS output end Proof for theBenchmark
% 1.59/0.56  % (17262)------------------------------
% 1.59/0.56  % (17262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (17262)Termination reason: Refutation
% 1.59/0.56  
% 1.59/0.56  % (17262)Memory used [KB]: 6524
% 1.59/0.56  % (17262)Time elapsed: 0.147 s
% 1.59/0.56  % (17262)------------------------------
% 1.59/0.56  % (17262)------------------------------
% 1.59/0.57  % (17246)Success in time 0.213 s
%------------------------------------------------------------------------------
