%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0295+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 104 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  184 ( 612 expanded)
%              Number of equality atoms :   41 ( 134 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2190,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1845,f1941,f1933,f2069])).

fof(f2069,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK31(X0,X1,sK5),sK4)
      | ~ r2_hidden(sK5,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK30(X0,X1,sK5),sK3) ) ),
    inference(resolution,[],[f1585,f1392])).

fof(f1392,plain,(
    ! [X4,X5] :
      ( ~ sQ41_eqProxy(k4_tarski(X4,X5),sK5)
      | ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(equality_proxy_replacement,[],[f729,f1376])).

fof(f1376,plain,(
    ! [X1,X0] :
      ( sQ41_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ41_eqProxy])])).

fof(f729,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK5
      | ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f580])).

fof(f580,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK5
        | ~ r2_hidden(X5,sK4)
        | ~ r2_hidden(X4,sK3) )
    & r2_hidden(sK5,sK2)
    & r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f402,f579])).

fof(f579,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK5
          | ~ r2_hidden(X5,sK4)
          | ~ r2_hidden(X4,sK3) )
      & r2_hidden(sK5,sK2)
      & r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f402,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f314])).

fof(f314,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f313])).

fof(f313,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f1585,plain,(
    ! [X0,X8,X1] :
      ( sQ41_eqProxy(k4_tarski(sK30(X0,X1,X8),sK31(X0,X1,X8)),X8)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f1314,f1376])).

fof(f1314,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK30(X0,X1,X8),sK31(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1057])).

fof(f1057,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK30(X0,X1,X8),sK31(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f660])).

fof(f660,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK27(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK27(X0,X1,X2),X2) )
          & ( ( sK27(X0,X1,X2) = k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2))
              & r2_hidden(sK29(X0,X1,X2),X1)
              & r2_hidden(sK28(X0,X1,X2),X0) )
            | r2_hidden(sK27(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK30(X0,X1,X8),sK31(X0,X1,X8)) = X8
                & r2_hidden(sK31(X0,X1,X8),X1)
                & r2_hidden(sK30(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28,sK29,sK30,sK31])],[f656,f659,f658,f657])).

fof(f657,plain,(
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
              ( k4_tarski(X4,X5) != sK27(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK27(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK27(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK27(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f658,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK27(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK27(X0,X1,X2) = k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2))
        & r2_hidden(sK29(X0,X1,X2),X1)
        & r2_hidden(sK28(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f659,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK30(X0,X1,X8),sK31(X0,X1,X8)) = X8
        & r2_hidden(sK31(X0,X1,X8),X1)
        & r2_hidden(sK30(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f656,plain,(
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
    inference(rectify,[],[f655])).

fof(f655,plain,(
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

fof(f1933,plain,(
    r2_hidden(sK31(sK3,sK4,sK5),sK4) ),
    inference(resolution,[],[f1315,f1845])).

fof(f1315,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK31(X0,X1,X8),X1) ) ),
    inference(equality_resolution,[],[f1056])).

fof(f1056,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK31(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f660])).

fof(f1941,plain,(
    r2_hidden(sK30(sK3,sK4,sK5),sK3) ),
    inference(resolution,[],[f1316,f1845])).

fof(f1316,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK30(X0,X1,X8),X0) ) ),
    inference(equality_resolution,[],[f1055])).

fof(f1055,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK30(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f660])).

fof(f1845,plain,(
    r2_hidden(sK5,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f1838,f727])).

fof(f727,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f580])).

fof(f1838,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | r2_hidden(sK5,X0) ) ),
    inference(resolution,[],[f894,f728])).

fof(f728,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f580])).

fof(f894,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f611])).

fof(f611,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK15(X0,X1),X1)
          & r2_hidden(sK15(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f609,f610])).

fof(f610,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK15(X0,X1),X1)
        & r2_hidden(sK15(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f609,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f608])).

fof(f608,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f454])).

fof(f454,plain,(
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
%------------------------------------------------------------------------------
