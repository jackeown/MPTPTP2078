%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0325+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 185 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  302 ( 751 expanded)
%              Number of equality atoms :   42 ( 105 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4609,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1968,f2357,f2829,f3239,f4531,f4606,f4608])).

fof(f4608,plain,
    ( spl65_1
    | ~ spl65_10 ),
    inference(avatar_contradiction_clause,[],[f4607])).

fof(f4607,plain,
    ( $false
    | spl65_1
    | ~ spl65_10 ),
    inference(subsumption_resolution,[],[f1963,f3250])).

fof(f3250,plain,
    ( r1_tarski(sK4,sK6)
    | ~ spl65_10 ),
    inference(duplicate_literal_removal,[],[f3246])).

fof(f3246,plain,
    ( r1_tarski(sK4,sK6)
    | r1_tarski(sK4,sK6)
    | ~ spl65_10 ),
    inference(resolution,[],[f2836,f1045])).

fof(f1045,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK27(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f706])).

fof(f706,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK27(X0,X1),X1)
          & r2_hidden(sK27(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f704,f705])).

fof(f705,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK27(X0,X1),X1)
        & r2_hidden(sK27(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f704,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f703])).

fof(f703,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f508])).

fof(f508,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2836,plain,
    ( ! [X4] :
        ( r2_hidden(sK27(sK4,X4),sK6)
        | r1_tarski(sK4,X4) )
    | ~ spl65_10 ),
    inference(resolution,[],[f2353,f1044])).

fof(f1044,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK27(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f706])).

fof(f2353,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | r2_hidden(X1,sK6) )
    | ~ spl65_10 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f2352,plain,
    ( spl65_10
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | r2_hidden(X1,sK6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl65_10])])).

fof(f1963,plain,
    ( ~ r1_tarski(sK4,sK6)
    | spl65_1 ),
    inference(avatar_component_clause,[],[f1961])).

fof(f1961,plain,
    ( spl65_1
  <=> r1_tarski(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl65_1])])).

fof(f4606,plain,
    ( spl65_2
    | ~ spl65_26 ),
    inference(avatar_contradiction_clause,[],[f4605])).

fof(f4605,plain,
    ( $false
    | spl65_2
    | ~ spl65_26 ),
    inference(subsumption_resolution,[],[f4604,f1967])).

fof(f1967,plain,
    ( ~ r1_tarski(sK5,sK7)
    | spl65_2 ),
    inference(avatar_component_clause,[],[f1965])).

fof(f1965,plain,
    ( spl65_2
  <=> r1_tarski(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl65_2])])).

fof(f4604,plain,
    ( r1_tarski(sK5,sK7)
    | ~ spl65_26 ),
    inference(duplicate_literal_removal,[],[f4600])).

fof(f4600,plain,
    ( r1_tarski(sK5,sK7)
    | r1_tarski(sK5,sK7)
    | ~ spl65_26 ),
    inference(resolution,[],[f4538,f1045])).

fof(f4538,plain,
    ( ! [X4] :
        ( r2_hidden(sK27(sK5,X4),sK7)
        | r1_tarski(sK5,X4) )
    | ~ spl65_26 ),
    inference(resolution,[],[f4530,f1044])).

fof(f4530,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK7) )
    | ~ spl65_26 ),
    inference(avatar_component_clause,[],[f4529])).

fof(f4529,plain,
    ( spl65_26
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl65_26])])).

fof(f4531,plain,
    ( spl65_18
    | spl65_26 ),
    inference(avatar_split_clause,[],[f2338,f4529,f2873])).

fof(f2873,plain,
    ( spl65_18
  <=> ! [X7] : ~ r2_hidden(X7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl65_18])])).

fof(f2338,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK5)
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(X2,sK7) ) ),
    inference(resolution,[],[f1999,f1379])).

fof(f1379,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f814])).

fof(f814,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f813])).

fof(f813,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1999,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7))
      | ~ r2_hidden(X1,sK5)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f1983,f1380])).

fof(f1380,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f814])).

fof(f1983,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
      | r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) ) ),
    inference(resolution,[],[f848,f1043])).

fof(f1043,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f706])).

fof(f848,plain,(
    r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f656])).

fof(f656,plain,
    ( ( ~ r1_tarski(sK5,sK7)
      | ~ r1_tarski(sK4,sK6) )
    & k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    & r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f444,f655])).

fof(f655,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK5,sK7)
        | ~ r1_tarski(sK4,sK6) )
      & k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
      & r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f444,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f443])).

fof(f443,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f350])).

fof(f350,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f349])).

fof(f349,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f3239,plain,(
    ~ spl65_18 ),
    inference(avatar_contradiction_clause,[],[f3238])).

fof(f3238,plain,
    ( $false
    | ~ spl65_18 ),
    inference(resolution,[],[f3205,f1956])).

fof(f1956,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f1583,f1603])).

fof(f1603,plain,(
    ! [X0] :
      ( sQ64_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f882,f1567])).

fof(f1567,plain,(
    ! [X1,X0] :
      ( sQ64_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ64_eqProxy])])).

fof(f882,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f447])).

fof(f447,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1583,plain,(
    ~ sQ64_eqProxy(k1_xboole_0,k2_zfmisc_1(sK4,sK5)) ),
    inference(equality_proxy_replacement,[],[f849,f1567])).

fof(f849,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f656])).

fof(f3205,plain,
    ( ! [X13] : v1_xboole_0(k2_zfmisc_1(sK4,X13))
    | ~ spl65_18 ),
    inference(resolution,[],[f2893,f887])).

fof(f887,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f660])).

fof(f660,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f658,f659])).

fof(f659,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f658,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f657])).

fof(f657,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2893,plain,
    ( ! [X12,X13] : ~ r2_hidden(X12,k2_zfmisc_1(sK4,X13))
    | ~ spl65_18 ),
    inference(resolution,[],[f2874,f1510])).

fof(f1510,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK44(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1225])).

fof(f1225,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK44(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f764])).

fof(f764,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK41(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK41(X0,X1,X2),X2) )
          & ( ( sK41(X0,X1,X2) = k4_tarski(sK42(X0,X1,X2),sK43(X0,X1,X2))
              & r2_hidden(sK43(X0,X1,X2),X1)
              & r2_hidden(sK42(X0,X1,X2),X0) )
            | r2_hidden(sK41(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK44(X0,X1,X8),sK45(X0,X1,X8)) = X8
                & r2_hidden(sK45(X0,X1,X8),X1)
                & r2_hidden(sK44(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK41,sK42,sK43,sK44,sK45])],[f760,f763,f762,f761])).

fof(f761,plain,(
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
              ( k4_tarski(X4,X5) != sK41(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK41(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK41(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK41(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f762,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK41(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK41(X0,X1,X2) = k4_tarski(sK42(X0,X1,X2),sK43(X0,X1,X2))
        & r2_hidden(sK43(X0,X1,X2),X1)
        & r2_hidden(sK42(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f763,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK44(X0,X1,X8),sK45(X0,X1,X8)) = X8
        & r2_hidden(sK45(X0,X1,X8),X1)
        & r2_hidden(sK44(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f760,plain,(
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
    inference(rectify,[],[f759])).

fof(f759,plain,(
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
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f2874,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK4)
    | ~ spl65_18 ),
    inference(avatar_component_clause,[],[f2873])).

fof(f2829,plain,(
    ~ spl65_11 ),
    inference(avatar_contradiction_clause,[],[f2828])).

fof(f2828,plain,
    ( $false
    | ~ spl65_11 ),
    inference(resolution,[],[f2795,f1956])).

fof(f2795,plain,
    ( ! [X13] : v1_xboole_0(k2_zfmisc_1(X13,sK5))
    | ~ spl65_11 ),
    inference(resolution,[],[f2422,f887])).

fof(f2422,plain,
    ( ! [X39,X40] : ~ r2_hidden(X39,k2_zfmisc_1(X40,sK5))
    | ~ spl65_11 ),
    inference(resolution,[],[f2356,f1509])).

fof(f1509,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK45(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1226])).

fof(f1226,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK45(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f764])).

fof(f2356,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl65_11 ),
    inference(avatar_component_clause,[],[f2355])).

fof(f2355,plain,
    ( spl65_11
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl65_11])])).

fof(f2357,plain,
    ( spl65_10
    | spl65_11 ),
    inference(avatar_split_clause,[],[f2337,f2355,f2352])).

fof(f2337,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5)
      | ~ r2_hidden(X1,sK4)
      | r2_hidden(X1,sK6) ) ),
    inference(resolution,[],[f1999,f1378])).

fof(f1378,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f814])).

fof(f1968,plain,
    ( ~ spl65_1
    | ~ spl65_2 ),
    inference(avatar_split_clause,[],[f850,f1965,f1961])).

fof(f850,plain,
    ( ~ r1_tarski(sK5,sK7)
    | ~ r1_tarski(sK4,sK6) ),
    inference(cnf_transformation,[],[f656])).
%------------------------------------------------------------------------------
