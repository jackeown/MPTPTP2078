%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0438+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  231 ( 312 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1712,f1717,f1847,f1852,f4179,f4180,f4543])).

fof(f4543,plain,
    ( spl81_11
    | ~ spl81_106
    | ~ spl81_107 ),
    inference(avatar_contradiction_clause,[],[f4542])).

fof(f4542,plain,
    ( $false
    | spl81_11
    | ~ spl81_106
    | ~ spl81_107 ),
    inference(subsumption_resolution,[],[f4541,f4177])).

fof(f4177,plain,
    ( r2_hidden(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | ~ spl81_107 ),
    inference(avatar_component_clause,[],[f4175])).

fof(f4175,plain,
    ( spl81_107
  <=> r2_hidden(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl81_107])])).

fof(f4541,plain,
    ( ~ r2_hidden(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | spl81_11
    | ~ spl81_106 ),
    inference(subsumption_resolution,[],[f4324,f4172])).

fof(f4172,plain,
    ( r2_hidden(sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl81_106 ),
    inference(avatar_component_clause,[],[f4170])).

fof(f4170,plain,
    ( spl81_106
  <=> r2_hidden(sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl81_106])])).

fof(f4324,plain,
    ( ~ r2_hidden(sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ r2_hidden(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | spl81_11 ),
    inference(resolution,[],[f1846,f1527])).

fof(f1527,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1053])).

fof(f1053,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1052])).

fof(f1052,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1846,plain,
    ( ~ r2_hidden(k4_tarski(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl81_11 ),
    inference(avatar_component_clause,[],[f1844])).

fof(f1844,plain,
    ( spl81_11
  <=> r2_hidden(k4_tarski(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl81_11])])).

fof(f4180,plain,
    ( spl81_107
    | ~ spl81_12 ),
    inference(avatar_split_clause,[],[f3797,f1849,f4175])).

fof(f1849,plain,
    ( spl81_12
  <=> r2_hidden(k4_tarski(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl81_12])])).

fof(f3797,plain,
    ( r2_hidden(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | ~ spl81_12 ),
    inference(unit_resulting_resolution,[],[f1851,f1606])).

fof(f1606,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f1159])).

fof(f1159,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f926])).

fof(f926,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f922,f925,f924,f923])).

fof(f923,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f924,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f925,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f922,plain,(
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
    inference(rectify,[],[f921])).

fof(f921,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1851,plain,
    ( r2_hidden(k4_tarski(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)
    | ~ spl81_12 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f4179,plain,
    ( spl81_106
    | ~ spl81_12 ),
    inference(avatar_split_clause,[],[f3798,f1849,f4170])).

fof(f3798,plain,
    ( r2_hidden(sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl81_12 ),
    inference(unit_resulting_resolution,[],[f1851,f1604])).

fof(f1604,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f1153])).

fof(f1153,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f916])).

fof(f916,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f912,f915,f914,f913])).

fof(f913,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f914,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f915,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f912,plain,(
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
    inference(rectify,[],[f911])).

fof(f911,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1852,plain,
    ( spl81_12
    | spl81_1
    | ~ spl81_2 ),
    inference(avatar_split_clause,[],[f1811,f1714,f1709,f1849])).

fof(f1709,plain,
    ( spl81_1
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl81_1])])).

fof(f1714,plain,
    ( spl81_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl81_2])])).

fof(f1811,plain,
    ( r2_hidden(k4_tarski(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)
    | spl81_1
    | ~ spl81_2 ),
    inference(unit_resulting_resolution,[],[f1716,f1711,f1171])).

fof(f1171,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f930])).

fof(f930,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f928,f929])).

fof(f929,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f928,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f927])).

fof(f927,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f718])).

fof(f718,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f640])).

fof(f640,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f1711,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl81_1 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f1716,plain,
    ( v1_relat_1(sK0)
    | ~ spl81_2 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1847,plain,
    ( ~ spl81_11
    | spl81_1
    | ~ spl81_2 ),
    inference(avatar_split_clause,[],[f1812,f1714,f1709,f1844])).

fof(f1812,plain,
    ( ~ r2_hidden(k4_tarski(sK12(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK13(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl81_1
    | ~ spl81_2 ),
    inference(unit_resulting_resolution,[],[f1716,f1711,f1172])).

fof(f1172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f930])).

fof(f1717,plain,(
    spl81_2 ),
    inference(avatar_split_clause,[],[f1081,f1714])).

fof(f1081,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f896])).

fof(f896,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f662,f895])).

fof(f895,plain,
    ( ? [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f662,plain,(
    ? [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f655])).

fof(f655,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f1712,plain,(
    ~ spl81_1 ),
    inference(avatar_split_clause,[],[f1082,f1709])).

fof(f1082,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f896])).
%------------------------------------------------------------------------------
