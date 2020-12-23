%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0697+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:29 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 208 expanded)
%              Number of leaves         :   25 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  500 (1032 expanded)
%              Number of equality atoms :   82 ( 159 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f143,f148,f173,f181,f244,f249,f252,f481,f490])).

fof(f490,plain,
    ( sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)))
    | r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),sK0)
    | ~ r2_hidden(sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

% (11877)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (11848)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f481,plain,
    ( spl9_25
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f461,f246,f236,f175,f85,f80,f75,f477])).

fof(f477,plain,
    ( spl9_25
  <=> sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f75,plain,
    ( spl9_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f80,plain,
    ( spl9_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f85,plain,
    ( spl9_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f175,plain,
    ( spl9_8
  <=> r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f236,plain,
    ( spl9_11
  <=> k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)) = k1_funct_1(sK1,sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f246,plain,
    ( spl9_13
  <=> r2_hidden(sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f461,plain,
    ( sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f87,f82,f77,f177,f248,f238,f40])).

fof(f40,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X4) != k1_funct_1(X0,X3)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X3)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X3)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f238,plain,
    ( k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)) = k1_funct_1(sK1,sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f248,plain,
    ( r2_hidden(sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))),k1_relat_1(sK1))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f246])).

fof(f177,plain,
    ( r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f77,plain,
    ( v2_funct_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f82,plain,
    ( v1_funct_1(sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f252,plain,
    ( spl9_11
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f251,f170,f85,f80,f236])).

fof(f170,plain,
    ( spl9_7
  <=> r2_hidden(k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f251,plain,
    ( k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)) = k1_funct_1(sK1,sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f250,f87])).

fof(f250,plain,
    ( k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)) = k1_funct_1(sK1,sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))))
    | ~ v1_relat_1(sK1)
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f225,f82])).

fof(f225,plain,
    ( k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)) = k1_funct_1(sK1,sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_7 ),
    inference(resolution,[],[f172,f66])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f172,plain,
    ( r2_hidden(k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),k9_relat_1(sK1,sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f249,plain,
    ( spl9_13
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f219,f170,f85,f80,f246])).

fof(f219,plain,
    ( r2_hidden(sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))),k1_relat_1(sK1))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f87,f82,f172,f68])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f244,plain,
    ( spl9_12
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f220,f170,f85,f80,f241])).

fof(f241,plain,
    ( spl9_12
  <=> r2_hidden(sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f220,plain,
    ( r2_hidden(sK7(sK1,sK0,k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))),sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f87,f82,f172,f67])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f181,plain,
    ( spl9_8
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f180,f145,f85,f80,f175])).

fof(f145,plain,
    ( spl9_6
  <=> r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f180,plain,
    ( r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f179,f87])).

fof(f179,plain,
    ( r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f158,f82])).

fof(f158,plain,
    ( r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f147,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK4(X0,X1,X2)),X1)
                | ~ r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK4(X0,X1,X2)),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK4(X0,X1,X2)),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK4(X0,X1,X2)),X1)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f147,plain,
    ( r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f173,plain,
    ( spl9_7
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f157,f145,f85,f80,f170])).

fof(f157,plain,
    ( r2_hidden(k1_funct_1(sK1,sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),k9_relat_1(sK1,sK0))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f87,f82,f147,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,
    ( spl9_6
    | spl9_1 ),
    inference(avatar_split_clause,[],[f128,f70,f145])).

fof(f70,plain,
    ( spl9_1
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f128,plain,
    ( r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f72,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f143,plain,
    ( ~ spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f129,f70,f140])).

fof(f140,plain,
    ( spl9_5
  <=> r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f129,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),sK0)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f72,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f83,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
