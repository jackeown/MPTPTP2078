%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0589+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
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
fof(f1673,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1375,f1381,f1578,f1655,f1671])).

fof(f1671,plain,
    ( spl32_1
    | ~ spl32_7 ),
    inference(avatar_contradiction_clause,[],[f1670])).

fof(f1670,plain,
    ( $false
    | spl32_1
    | ~ spl32_7 ),
    inference(subsumption_resolution,[],[f1656,f1374])).

fof(f1374,plain,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0)
    | spl32_1 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1372,plain,
    ( spl32_1
  <=> r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).

fof(f1656,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0)
    | ~ spl32_7 ),
    inference(resolution,[],[f1654,f1161])).

fof(f1161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1029,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1027,f1028])).

fof(f1028,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1026])).

fof(f1026,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f894])).

fof(f894,plain,(
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

fof(f1654,plain,
    ( r2_hidden(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),sK0)
    | ~ spl32_7 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f1652,plain,
    ( spl32_7
  <=> r2_hidden(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_7])])).

fof(f1655,plain,
    ( spl32_7
    | ~ spl32_6 ),
    inference(avatar_split_clause,[],[f1583,f1575,f1652])).

fof(f1575,plain,
    ( spl32_6
  <=> r2_hidden(k4_tarski(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),sK11(k2_zfmisc_1(sK0,sK1),sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0))),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_6])])).

fof(f1583,plain,
    ( r2_hidden(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),sK0)
    | ~ spl32_6 ),
    inference(resolution,[],[f1577,f1272])).

fof(f1272,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1074])).

fof(f1074,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1073])).

fof(f1073,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1577,plain,
    ( r2_hidden(k4_tarski(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),sK11(k2_zfmisc_1(sK0,sK1),sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0))),k2_zfmisc_1(sK0,sK1))
    | ~ spl32_6 ),
    inference(avatar_component_clause,[],[f1575])).

fof(f1578,plain,
    ( spl32_6
    | ~ spl32_2 ),
    inference(avatar_split_clause,[],[f1383,f1378,f1575])).

fof(f1378,plain,
    ( spl32_2
  <=> r2_hidden(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),k1_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).

fof(f1383,plain,
    ( r2_hidden(k4_tarski(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),sK11(k2_zfmisc_1(sK0,sK1),sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0))),k2_zfmisc_1(sK0,sK1))
    | ~ spl32_2 ),
    inference(resolution,[],[f1380,f1359])).

fof(f1359,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f1201])).

fof(f1201,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1047])).

fof(f1047,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f1043,f1046,f1045,f1044])).

fof(f1044,plain,(
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

fof(f1045,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1046,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1043,plain,(
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
    inference(rectify,[],[f1042])).

fof(f1042,plain,(
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
    inference(nnf_transformation,[],[f650])).

fof(f650,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1380,plain,
    ( r2_hidden(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl32_2 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f1381,plain,
    ( spl32_2
    | spl32_1 ),
    inference(avatar_split_clause,[],[f1376,f1372,f1378])).

fof(f1376,plain,
    ( r2_hidden(sK5(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0),k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | spl32_1 ),
    inference(resolution,[],[f1374,f1160])).

fof(f1160,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1375,plain,(
    ~ spl32_1 ),
    inference(avatar_split_clause,[],[f1090,f1372])).

fof(f1090,plain,(
    ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0) ),
    inference(cnf_transformation,[],[f1002])).

fof(f1002,plain,(
    ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f851,f1001])).

fof(f1001,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)
   => ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK0) ),
    introduced(choice_axiom,[])).

fof(f851,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(ennf_transformation,[],[f784])).

fof(f784,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(negated_conjecture,[],[f783])).

fof(f783,conjecture,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
%------------------------------------------------------------------------------
