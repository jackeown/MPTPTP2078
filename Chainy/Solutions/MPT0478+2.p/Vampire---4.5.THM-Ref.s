%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0478+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 ( 384 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3838,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1993,f3312,f3740,f3809,f3837])).

fof(f3837,plain,
    ( ~ spl98_26
    | spl98_27 ),
    inference(avatar_contradiction_clause,[],[f3836])).

fof(f3836,plain,
    ( $false
    | ~ spl98_26
    | spl98_27 ),
    inference(subsumption_resolution,[],[f3815,f3741])).

fof(f3741,plain,
    ( r2_hidden(sK29(k6_relat_1(sK0),sK1),sK0)
    | ~ spl98_26 ),
    inference(unit_resulting_resolution,[],[f1245,f3739,f1829])).

fof(f1829,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1236])).

fof(f1236,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1022])).

fof(f1022,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK2(X0,X1) != sK3(X0,X1)
              | ~ r2_hidden(sK2(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( ( sK2(X0,X1) = sK3(X0,X1)
                & r2_hidden(sK2(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f1020,f1021])).

fof(f1021,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK2(X0,X1) != sK3(X0,X1)
          | ~ r2_hidden(sK2(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( ( sK2(X0,X1) = sK3(X0,X1)
            & r2_hidden(sK2(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1020,plain,(
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
    inference(rectify,[],[f1019])).

fof(f1019,plain,(
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
    inference(flattening,[],[f1018])).

fof(f1018,plain,(
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
    inference(nnf_transformation,[],[f728])).

fof(f728,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f3739,plain,
    ( r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK30(k6_relat_1(sK0),sK1)),k6_relat_1(sK0))
    | ~ spl98_26 ),
    inference(avatar_component_clause,[],[f3737])).

fof(f3737,plain,
    ( spl98_26
  <=> r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK30(k6_relat_1(sK0),sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl98_26])])).

fof(f1245,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f3815,plain,
    ( ~ r2_hidden(sK29(k6_relat_1(sK0),sK1),sK0)
    | spl98_27 ),
    inference(unit_resulting_resolution,[],[f3808,f1230])).

fof(f1230,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,X2),sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f1015])).

fof(f1015,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),sK1)
    & ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK1)
        | ~ r2_hidden(X2,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f725,f1014])).

fof(f1014,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        & ! [X2] :
            ( r2_hidden(k4_tarski(X2,X2),X1)
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_relat_1(sK0),sK1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),sK1)
          | ~ r2_hidden(X2,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f725,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f724])).

fof(f724,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f718])).

fof(f718,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ( r2_hidden(X2,X0)
             => r2_hidden(k4_tarski(X2,X2),X1) )
         => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f717])).

fof(f717,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(f3808,plain,
    ( ~ r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK29(k6_relat_1(sK0),sK1)),sK1)
    | spl98_27 ),
    inference(avatar_component_clause,[],[f3806])).

fof(f3806,plain,
    ( spl98_27
  <=> r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK29(k6_relat_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl98_27])])).

fof(f3809,plain,
    ( ~ spl98_27
    | spl98_25
    | ~ spl98_26 ),
    inference(avatar_split_clause,[],[f3778,f3737,f3309,f3806])).

fof(f3309,plain,
    ( spl98_25
  <=> r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK30(k6_relat_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl98_25])])).

fof(f3778,plain,
    ( ~ r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK29(k6_relat_1(sK0),sK1)),sK1)
    | spl98_25
    | ~ spl98_26 ),
    inference(backward_demodulation,[],[f3311,f3742])).

fof(f3742,plain,
    ( sK29(k6_relat_1(sK0),sK1) = sK30(k6_relat_1(sK0),sK1)
    | ~ spl98_26 ),
    inference(unit_resulting_resolution,[],[f1245,f3739,f1828])).

fof(f1828,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1237])).

fof(f1237,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1022])).

fof(f3311,plain,
    ( ~ r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK30(k6_relat_1(sK0),sK1)),sK1)
    | spl98_25 ),
    inference(avatar_component_clause,[],[f3309])).

fof(f3740,plain,
    ( spl98_26
    | spl98_2 ),
    inference(avatar_split_clause,[],[f2243,f1990,f3737])).

fof(f1990,plain,
    ( spl98_2
  <=> r1_tarski(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl98_2])])).

fof(f2243,plain,
    ( r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK30(k6_relat_1(sK0),sK1)),k6_relat_1(sK0))
    | spl98_2 ),
    inference(unit_resulting_resolution,[],[f1992,f1245,f1307])).

fof(f1307,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK29(X0,X1),sK30(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1069])).

fof(f1069,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK29(X0,X1),sK30(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK29(X0,X1),sK30(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29,sK30])],[f1067,f1068])).

fof(f1068,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK29(X0,X1),sK30(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK29(X0,X1),sK30(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1067,plain,(
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
    inference(rectify,[],[f1066])).

fof(f1066,plain,(
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
    inference(nnf_transformation,[],[f742])).

fof(f742,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f1992,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),sK1)
    | spl98_2 ),
    inference(avatar_component_clause,[],[f1990])).

fof(f3312,plain,
    ( ~ spl98_25
    | spl98_2 ),
    inference(avatar_split_clause,[],[f2245,f1990,f3309])).

fof(f2245,plain,
    ( ~ r2_hidden(k4_tarski(sK29(k6_relat_1(sK0),sK1),sK30(k6_relat_1(sK0),sK1)),sK1)
    | spl98_2 ),
    inference(unit_resulting_resolution,[],[f1245,f1992,f1308])).

fof(f1308,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK29(X0,X1),sK30(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1069])).

fof(f1993,plain,(
    ~ spl98_2 ),
    inference(avatar_split_clause,[],[f1231,f1990])).

fof(f1231,plain,(
    ~ r1_tarski(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f1015])).
%------------------------------------------------------------------------------
