%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0590+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 2.85s
% Output     : Refutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 189 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1368,f1374,f1568,f1645,f1661])).

fof(f1661,plain,
    ( spl32_1
    | ~ spl32_7 ),
    inference(avatar_contradiction_clause,[],[f1660])).

fof(f1660,plain,
    ( $false
    | spl32_1
    | ~ spl32_7 ),
    inference(subsumption_resolution,[],[f1646,f1367])).

fof(f1367,plain,
    ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)
    | spl32_1 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1365,plain,
    ( spl32_1
  <=> r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).

fof(f1646,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)
    | ~ spl32_7 ),
    inference(resolution,[],[f1644,f1157])).

fof(f1157,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1026])).

fof(f1026,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1024,f1025])).

fof(f1025,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1024,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1023])).

fof(f1023,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f895])).

fof(f895,plain,(
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

fof(f1644,plain,
    ( r2_hidden(sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1),sK1)
    | ~ spl32_7 ),
    inference(avatar_component_clause,[],[f1642])).

fof(f1642,plain,
    ( spl32_7
  <=> r2_hidden(sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_7])])).

fof(f1645,plain,
    ( spl32_7
    | ~ spl32_6 ),
    inference(avatar_split_clause,[],[f1574,f1565,f1642])).

fof(f1565,plain,
    ( spl32_6
  <=> r2_hidden(k4_tarski(sK11(k2_zfmisc_1(sK0,sK1),sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)),sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_6])])).

fof(f1574,plain,
    ( r2_hidden(sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1),sK1)
    | ~ spl32_6 ),
    inference(resolution,[],[f1567,f1265])).

fof(f1265,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1070])).

fof(f1070,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1069])).

fof(f1069,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f325])).

fof(f325,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f1567,plain,
    ( r2_hidden(k4_tarski(sK11(k2_zfmisc_1(sK0,sK1),sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)),sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl32_6 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1568,plain,
    ( spl32_6
    | ~ spl32_2 ),
    inference(avatar_split_clause,[],[f1376,f1371,f1565])).

fof(f1371,plain,
    ( spl32_2
  <=> r2_hidden(sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).

fof(f1376,plain,
    ( r2_hidden(k4_tarski(sK11(k2_zfmisc_1(sK0,sK1),sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)),sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl32_2 ),
    inference(resolution,[],[f1373,f1352])).

fof(f1352,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f1197])).

fof(f1197,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1044])).

fof(f1044,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f1040,f1043,f1042,f1041])).

fof(f1041,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1042,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1043,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1040,plain,(
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
    inference(rectify,[],[f1039])).

fof(f1039,plain,(
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
    inference(nnf_transformation,[],[f651])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1373,plain,
    ( r2_hidden(sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl32_2 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f1374,plain,
    ( spl32_2
    | spl32_1 ),
    inference(avatar_split_clause,[],[f1369,f1365,f1371])).

fof(f1369,plain,
    ( r2_hidden(sK5(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | spl32_1 ),
    inference(resolution,[],[f1367,f1156])).

fof(f1156,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1026])).

fof(f1368,plain,(
    ~ spl32_1 ),
    inference(avatar_split_clause,[],[f1086,f1365])).

fof(f1086,plain,(
    ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f999])).

fof(f999,plain,(
    ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f852,f998])).

fof(f998,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)
   => ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK1)),sK1) ),
    introduced(choice_axiom,[])).

fof(f852,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f785])).

fof(f785,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f784])).

fof(f784,conjecture,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
%------------------------------------------------------------------------------
