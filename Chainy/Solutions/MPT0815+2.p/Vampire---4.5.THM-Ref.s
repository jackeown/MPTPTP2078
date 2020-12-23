%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0815+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   26 (  38 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 176 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2350,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2349,f1451])).

fof(f1451,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1324])).

fof(f1324,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1218,f1323])).

fof(f1323,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1218,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1217])).

fof(f1217,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1215])).

fof(f1215,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f1214])).

fof(f1214,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

fof(f2349,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2331,f1452])).

fof(f1452,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f1324])).

fof(f2331,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f1962,f1696])).

fof(f1696,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f1695])).

fof(f1695,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f1543])).

fof(f1543,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1380])).

fof(f1380,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK26(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK26(X0,X1,X2),X2) )
          & ( ( sK26(X0,X1,X2) = k4_tarski(sK27(X0,X1,X2),sK28(X0,X1,X2))
              & r2_hidden(sK28(X0,X1,X2),X1)
              & r2_hidden(sK27(X0,X1,X2),X0) )
            | r2_hidden(sK26(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK29(X0,X1,X8),sK30(X0,X1,X8)) = X8
                & r2_hidden(sK30(X0,X1,X8),X1)
                & r2_hidden(sK29(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27,sK28,sK29,sK30])],[f1376,f1379,f1378,f1377])).

fof(f1377,plain,(
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
              ( k4_tarski(X4,X5) != sK26(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK26(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK26(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK26(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1378,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK26(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK26(X0,X1,X2) = k4_tarski(sK27(X0,X1,X2),sK28(X0,X1,X2))
        & r2_hidden(sK28(X0,X1,X2),X1)
        & r2_hidden(sK27(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1379,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK29(X0,X1,X8),sK30(X0,X1,X8)) = X8
        & r2_hidden(sK30(X0,X1,X8),X1)
        & r2_hidden(sK29(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1376,plain,(
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
    inference(rectify,[],[f1375])).

fof(f1375,plain,(
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
    inference(nnf_transformation,[],[f286])).

fof(f286,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1962,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f1453,f1480])).

fof(f1480,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1236])).

fof(f1236,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f1453,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f1324])).
%------------------------------------------------------------------------------
