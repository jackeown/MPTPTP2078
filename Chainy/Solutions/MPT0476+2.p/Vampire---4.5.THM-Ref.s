%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0476+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 159 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  325 ( 824 expanded)
%              Number of equality atoms :   80 ( 230 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1985,f2033,f5211,f5215,f5608,f5761,f5837,f6728,f7144,f7520,f8034,f8249])).

fof(f8249,plain,
    ( ~ spl96_8
    | ~ spl96_525
    | ~ spl96_526 ),
    inference(avatar_split_clause,[],[f7968,f5857,f5854,f2013])).

fof(f2013,plain,
    ( spl96_8
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_8])])).

fof(f5854,plain,
    ( spl96_525
  <=> r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_525])])).

fof(f5857,plain,
    ( spl96_526
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_526])])).

fof(f7968,plain,
    ( ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl96_526 ),
    inference(resolution,[],[f5858,f1850])).

fof(f1850,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1849])).

fof(f1849,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f1268])).

fof(f1268,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1031])).

fof(f1031,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK9(X0,X1) != sK10(X0,X1)
              | ~ r2_hidden(sK9(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) )
            & ( ( sK9(X0,X1) = sK10(X0,X1)
                & r2_hidden(sK9(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f1029,f1030])).

fof(f1030,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK9(X0,X1) != sK10(X0,X1)
          | ~ r2_hidden(sK9(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) )
        & ( ( sK9(X0,X1) = sK10(X0,X1)
            & r2_hidden(sK9(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1029,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1028])).

fof(f1028,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f758])).

fof(f758,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f640])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f5858,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))
    | ~ spl96_526 ),
    inference(avatar_component_clause,[],[f5857])).

fof(f8034,plain,
    ( spl96_525
    | spl96_1
    | ~ spl96_526 ),
    inference(avatar_split_clause,[],[f7967,f5857,f1980,f5854])).

fof(f1980,plain,
    ( spl96_1
  <=> sK0 = k1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_1])])).

fof(f7967,plain,
    ( sK0 = k1_relat_1(k6_relat_1(sK0))
    | r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ spl96_526 ),
    inference(resolution,[],[f5858,f1259])).

fof(f1259,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1026])).

fof(f1026,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f1022,f1025,f1024,f1023])).

fof(f1023,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1024,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1025,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1022,plain,(
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
    inference(rectify,[],[f1021])).

fof(f1021,plain,(
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
    inference(nnf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f7520,plain,
    ( ~ spl96_8
    | spl96_526
    | spl96_525 ),
    inference(avatar_split_clause,[],[f7451,f5854,f5857,f2013])).

fof(f7451,plain,
    ( ! [X40] :
        ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK0),sK0),X40),k6_relat_1(sK0))
        | ~ v1_relat_1(k6_relat_1(sK0)) )
    | spl96_525 ),
    inference(resolution,[],[f5855,f1852])).

fof(f1852,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1266])).

fof(f1266,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1031])).

fof(f5855,plain,
    ( ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | spl96_525 ),
    inference(avatar_component_clause,[],[f5854])).

fof(f7144,plain,
    ( spl96_526
    | spl96_1
    | ~ spl96_525 ),
    inference(avatar_split_clause,[],[f7063,f5854,f1980,f5857])).

fof(f7063,plain,
    ( ! [X0] :
        ( sK0 = k1_relat_1(k6_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) )
    | ~ spl96_525 ),
    inference(resolution,[],[f5944,f1260])).

fof(f1260,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1026])).

fof(f5944,plain,
    ( r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ spl96_525 ),
    inference(avatar_component_clause,[],[f5854])).

fof(f6728,plain,
    ( spl96_53
    | spl96_2
    | spl96_34 ),
    inference(avatar_split_clause,[],[f6665,f2164,f1983,f2254])).

fof(f2254,plain,
    ( spl96_53
  <=> r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK0),sK1(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_53])])).

fof(f1983,plain,
    ( spl96_2
  <=> sK0 = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_2])])).

fof(f2164,plain,
    ( spl96_34
  <=> r2_hidden(sK1(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_34])])).

fof(f6665,plain,
    ( sK0 = k2_relat_1(k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK0),sK1(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | spl96_34 ),
    inference(resolution,[],[f2165,f1235])).

fof(f1235,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1015])).

fof(f1015,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f1011,f1014,f1013,f1012])).

fof(f1012,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1013,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1014,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1011,plain,(
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
    inference(rectify,[],[f1010])).

fof(f1010,plain,(
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
    inference(nnf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f2165,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK0),sK0),sK0)
    | spl96_34 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f5837,plain,
    ( sK1(k6_relat_1(sK0),sK0) != sK2(k6_relat_1(sK0),sK0)
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK0),sK0)
    | r2_hidden(sK1(k6_relat_1(sK0),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5761,plain,
    ( ~ spl96_8
    | ~ spl96_34
    | ~ spl96_35 ),
    inference(avatar_split_clause,[],[f5694,f2167,f2164,f2013])).

fof(f2167,plain,
    ( spl96_35
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK1(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_35])])).

fof(f5694,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK0),sK0),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl96_35 ),
    inference(resolution,[],[f2168,f1850])).

fof(f2168,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK1(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | ~ spl96_35 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f5608,plain,
    ( spl96_35
    | spl96_2
    | ~ spl96_34 ),
    inference(avatar_split_clause,[],[f5527,f2164,f1983,f2167])).

fof(f5527,plain,
    ( ! [X0] :
        ( sK0 = k2_relat_1(k6_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK1(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) )
    | ~ spl96_34 ),
    inference(resolution,[],[f2252,f1236])).

fof(f1236,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1015])).

fof(f2252,plain,
    ( r2_hidden(sK1(k6_relat_1(sK0),sK0),sK0)
    | ~ spl96_34 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f5215,plain,
    ( ~ spl96_8
    | spl96_454
    | ~ spl96_53 ),
    inference(avatar_split_clause,[],[f5119,f2254,f5213,f2013])).

fof(f5213,plain,
    ( spl96_454
  <=> sK1(k6_relat_1(sK0),sK0) = sK2(k6_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_454])])).

fof(f5119,plain,
    ( sK1(k6_relat_1(sK0),sK0) = sK2(k6_relat_1(sK0),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl96_53 ),
    inference(resolution,[],[f2255,f1851])).

fof(f1851,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1267])).

fof(f1267,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1031])).

fof(f2255,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK0),sK1(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | ~ spl96_53 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f5211,plain,
    ( ~ spl96_8
    | spl96_453
    | ~ spl96_53 ),
    inference(avatar_split_clause,[],[f5118,f2254,f5209,f2013])).

fof(f5209,plain,
    ( spl96_453
  <=> r2_hidden(sK2(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_453])])).

fof(f5118,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK0),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl96_53 ),
    inference(resolution,[],[f2255,f1852])).

fof(f2033,plain,(
    spl96_8 ),
    inference(avatar_contradiction_clause,[],[f2022])).

fof(f2022,plain,
    ( $false
    | spl96_8 ),
    inference(resolution,[],[f2014,f1272])).

fof(f1272,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f2014,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl96_8 ),
    inference(avatar_component_clause,[],[f2013])).

fof(f1985,plain,
    ( ~ spl96_1
    | ~ spl96_2 ),
    inference(avatar_split_clause,[],[f1226,f1983,f1980])).

fof(f1226,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | sK0 != k1_relat_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1009])).

fof(f1009,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | sK0 != k1_relat_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f722,f1008])).

fof(f1008,plain,
    ( ? [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != X0
        | k1_relat_1(k6_relat_1(X0)) != X0 )
   => ( sK0 != k2_relat_1(k6_relat_1(sK0))
      | sK0 != k1_relat_1(k6_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f722,plain,(
    ? [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | k1_relat_1(k6_relat_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f716])).

fof(f716,negated_conjecture,(
    ~ ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) = X0
        & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f715])).

fof(f715,conjecture,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
%------------------------------------------------------------------------------
