%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0488+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 162 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 ( 837 expanded)
%              Number of equality atoms :   22 (  65 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f966,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f817,f820,f822,f826,f849,f915,f928,f956,f965])).

fof(f965,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f964])).

fof(f964,plain,
    ( $false
    | spl10_3
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f825,f927,f958,f827])).

fof(f827,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f792,f805])).

fof(f805,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f794])).

fof(f794,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f771])).

% (5161)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% (5162)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% (5172)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% (5166)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
fof(f771,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK8(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X0)
                    & r2_hidden(sK8(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f769,f770])).

fof(f770,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X0)
            & r2_hidden(sK8(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f769,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f768])).

fof(f768,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f767])).

fof(f767,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f747])).

fof(f747,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f792,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f746])).

fof(f746,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f958,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK2)
    | spl10_3 ),
    inference(resolution,[],[f816,f802])).

fof(f802,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f783])).

fof(f783,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f766])).

fof(f766,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f762,f765,f764,f763])).

fof(f763,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f764,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f765,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f762,plain,(
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
    inference(rectify,[],[f761])).

% (5171)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
fof(f761,plain,(
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
    inference(nnf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f816,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f815])).

fof(f815,plain,
    ( spl10_3
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f927,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f926])).

fof(f926,plain,
    ( spl10_12
  <=> r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f825,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl10_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f956,plain,
    ( spl10_2
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f955,f926,f824,f812])).

fof(f812,plain,
    ( spl10_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f955,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f939,f825])).

fof(f939,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl10_12 ),
    inference(resolution,[],[f927,f889])).

fof(f889,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f806,f792])).

fof(f806,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f793])).

fof(f793,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f771])).

fof(f928,plain,
    ( spl10_12
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f923,f809,f926])).

fof(f809,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f923,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_1 ),
    inference(resolution,[],[f818,f803])).

fof(f803,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f782])).

fof(f782,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f766])).

fof(f818,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f809])).

fof(f915,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f908])).

fof(f908,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f825,f821,f848,f842,f906])).

fof(f906,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f804,f792])).

fof(f804,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f795])).

fof(f795,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f771])).

fof(f842,plain,
    ( ! [X3] : ~ r2_hidden(k4_tarski(sK0,X3),k7_relat_1(sK2,sK1))
    | spl10_1 ),
    inference(resolution,[],[f802,f810])).

fof(f810,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f809])).

fof(f848,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK2,sK0)),sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f847])).

fof(f847,plain,
    ( spl10_7
  <=> r2_hidden(k4_tarski(sK0,sK7(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f821,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f812])).

fof(f849,plain,
    ( spl10_7
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f843,f815,f847])).

fof(f843,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK2,sK0)),sK2)
    | ~ spl10_3 ),
    inference(resolution,[],[f803,f819])).

fof(f819,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f815])).

fof(f826,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f772,f824])).

fof(f772,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f755])).

fof(f755,plain,
    ( ( ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(sK0,k1_relat_1(sK2))
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f753,f754])).

fof(f754,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(sK0,k1_relat_1(sK2))
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f753,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f752])).

fof(f752,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f734])).

fof(f734,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <~> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f731])).

fof(f731,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        <=> ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f730])).

fof(f730,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f822,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f773,f812,f809])).

fof(f773,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f755])).

fof(f820,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f774,f815,f809])).

fof(f774,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f755])).

fof(f817,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f775,f815,f812,f809])).

fof(f775,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f755])).
%------------------------------------------------------------------------------
