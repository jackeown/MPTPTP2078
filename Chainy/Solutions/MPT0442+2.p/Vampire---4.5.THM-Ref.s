%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0442+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 167 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  250 ( 751 expanded)
%              Number of equality atoms :   18 (  64 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f774,f778,f1391,f1419])).

fof(f1419,plain,
    ( spl13_1
    | ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f1418])).

fof(f1418,plain,
    ( $false
    | spl13_1
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f770,f1399,f877])).

fof(f877,plain,(
    ! [X6,X5] :
      ( r1_tarski(k1_relat_1(X5),X6)
      | r2_hidden(k4_tarski(sK10(k1_relat_1(X5),X6),sK9(X5,sK10(k1_relat_1(X5),X6))),X5) ) ),
    inference(resolution,[],[f765,f744])).

fof(f744,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f711,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f709,f710])).

fof(f710,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f709,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f708])).

fof(f708,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f683])).

fof(f683,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f765,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f736])).

fof(f736,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f707])).

fof(f707,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f703,f706,f705,f704])).

fof(f704,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f705,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f706,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f703,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f702])).

fof(f702,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1399,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK10(k1_relat_1(sK0),k1_relat_1(sK1)),X0),sK0)
    | spl13_1
    | ~ spl13_3 ),
    inference(resolution,[],[f1392,f1135])).

fof(f1135,plain,
    ( ! [X14,X15] :
        ( r2_hidden(k4_tarski(X14,sK9(sK1,X14)),sK1)
        | ~ r2_hidden(k4_tarski(X14,X15),sK0) )
    | ~ spl13_3 ),
    inference(resolution,[],[f875,f806])).

fof(f806,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl13_3 ),
    inference(resolution,[],[f743,f777])).

fof(f777,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl13_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f743,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f875,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),X1)
      | r2_hidden(k4_tarski(X0,sK9(X1,X0)),X1) ) ),
    inference(resolution,[],[f765,f764])).

fof(f764,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f737])).

fof(f737,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f707])).

fof(f1392,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK10(k1_relat_1(sK0),k1_relat_1(sK1)),X0),sK1)
    | spl13_1 ),
    inference(resolution,[],[f770,f833])).

fof(f833,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_relat_1(X1))
      | ~ r2_hidden(k4_tarski(sK10(X0,k1_relat_1(X1)),X2),X1) ) ),
    inference(resolution,[],[f764,f745])).

fof(f745,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f770,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f769])).

fof(f769,plain,
    ( spl13_1
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1391,plain,
    ( spl13_2
    | ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f1390])).

fof(f1390,plain,
    ( $false
    | spl13_2
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f1377,f1315])).

fof(f1315,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK10(k2_relat_1(sK0),k2_relat_1(sK1))),sK0)
    | spl13_2
    | ~ spl13_3 ),
    inference(resolution,[],[f1247,f1128])).

fof(f1128,plain,
    ( ! [X14,X15] :
        ( r2_hidden(k4_tarski(sK4(sK1,X14),X14),sK1)
        | ~ r2_hidden(k4_tarski(X15,X14),sK0) )
    | ~ spl13_3 ),
    inference(resolution,[],[f871,f806])).

fof(f871,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X1),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),X1),X0) ) ),
    inference(resolution,[],[f763,f762])).

fof(f762,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f729])).

fof(f729,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f697])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f693,f696,f695,f694])).

fof(f694,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f695,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f696,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f693,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f692])).

fof(f692,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f763,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f728])).

fof(f728,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f697])).

fof(f1247,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK10(k2_relat_1(sK0),k2_relat_1(sK1))),sK1)
    | spl13_2 ),
    inference(resolution,[],[f773,f830])).

fof(f830,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,sK10(X1,k2_relat_1(X2))),X2) ) ),
    inference(resolution,[],[f762,f745])).

fof(f773,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f772])).

fof(f772,plain,
    ( spl13_2
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1377,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK10(k2_relat_1(sK0),k2_relat_1(sK1))),sK10(k2_relat_1(sK0),k2_relat_1(sK1))),sK0)
    | spl13_2 ),
    inference(resolution,[],[f873,f773])).

fof(f873,plain,(
    ! [X6,X5] :
      ( r1_tarski(k2_relat_1(X5),X6)
      | r2_hidden(k4_tarski(sK4(X5,sK10(k2_relat_1(X5),X6)),sK10(k2_relat_1(X5),X6)),X5) ) ),
    inference(resolution,[],[f763,f744])).

fof(f778,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f720,f776])).

fof(f720,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f691])).

fof(f691,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) )
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f666,f690,f689])).

fof(f689,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X1)) )
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f690,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
          | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X1)) )
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
        | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) )
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f666,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f665])).

fof(f665,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f662])).

fof(f662,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f661])).

fof(f661,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f774,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f721,f772,f769])).

fof(f721,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f691])).
%------------------------------------------------------------------------------
