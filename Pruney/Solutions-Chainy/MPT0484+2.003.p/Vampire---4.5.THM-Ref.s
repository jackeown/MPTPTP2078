%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 176 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  320 ( 660 expanded)
%              Number of equality atoms :   27 (  88 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f112,f127,f172])).

fof(f172,plain,
    ( ~ spl9_2
    | spl9_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl9_2
    | spl9_3 ),
    inference(subsumption_resolution,[],[f170,f106])).

fof(f106,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_3
  <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f170,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl9_2 ),
    inference(resolution,[],[f132,f139])).

fof(f139,plain,
    ( r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0)
    | ~ spl9_2 ),
    inference(resolution,[],[f137,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f135,f35])).

fof(f35,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f134,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X0)
        | ~ r1_tarski(k2_relat_1(sK1),X0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f131,f46])).

fof(f131,plain,
    ( r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),k2_relat_1(sK1))
    | ~ spl9_2 ),
    inference(resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_2
  <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f132,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X1)
        | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(X1))) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f130,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f130,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(X1)))
        | ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f103,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(f127,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f125,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f124,f98])).

fof(f98,plain,
    ( v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_1
  <=> v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f124,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f123,f121])).

fof(f121,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f115,f34])).

fof(f115,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(resolution,[],[f107,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f123,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f117,f58])).

fof(f58,plain,(
    ~ sQ8_eqProxy(sK1,k5_relat_1(sK1,k6_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f36,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f36,plain,(
    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,
    ( sQ8_eqProxy(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(resolution,[],[f107,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | sQ8_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f40,f57])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f112,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f110,plain,
    ( ~ v1_relat_1(sK1)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f109,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl9_1 ),
    inference(resolution,[],[f99,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f108,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f95,f105,f101,f97])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sQ8_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:50:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (27699)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (27691)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27696)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (27704)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (27685)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (27703)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (27688)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27687)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (27687)Refutation not found, incomplete strategy% (27687)------------------------------
% 0.21/0.52  % (27687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27687)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27687)Memory used [KB]: 10618
% 0.21/0.52  % (27687)Time elapsed: 0.106 s
% 0.21/0.52  % (27687)------------------------------
% 0.21/0.52  % (27687)------------------------------
% 0.21/0.52  % (27711)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (27712)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (27697)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (27707)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (27710)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (27707)Refutation not found, incomplete strategy% (27707)------------------------------
% 0.21/0.53  % (27707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27707)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27707)Memory used [KB]: 10618
% 0.21/0.53  % (27707)Time elapsed: 0.109 s
% 0.21/0.53  % (27707)------------------------------
% 0.21/0.53  % (27707)------------------------------
% 0.21/0.53  % (27689)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (27700)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (27714)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (27693)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (27713)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (27690)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (27702)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (27686)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (27695)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (27701)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (27694)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27692)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (27709)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (27705)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (27708)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (27698)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (27702)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f108,f112,f127,f172])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~spl9_2 | spl9_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    $false | (~spl9_2 | spl9_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | spl9_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl9_3 <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f132,f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f137,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f48,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X0)) ) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f135,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1)) => (sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f7])).
% 0.21/0.54  fof(f7,conjecture,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK1),X0) | r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X1) | ~r1_tarski(X0,X1)) ) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f134,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X0) | ~r1_tarski(k2_relat_1(sK1),X0)) ) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f131,f46])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),k2_relat_1(sK1)) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f103,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~spl9_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl9_2 <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X1) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(X1)))) ) | ~spl9_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(X1))) | ~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),X1) | ~v1_relat_1(sK1)) ) | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f103,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.21/0.54    inference(nnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ~spl9_1 | ~spl9_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    $false | (~spl9_1 | ~spl9_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f34])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ~v1_relat_1(sK1) | (~spl9_1 | ~spl9_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~spl9_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl9_1 <=> v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1) | ~spl9_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~spl9_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f34])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~v1_relat_1(sK1) | ~spl9_3),
% 0.21/0.54    inference(resolution,[],[f107,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | ~spl9_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1) | ~spl9_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~sQ8_eqProxy(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.21/0.54    inference(equality_proxy_replacement,[],[f36,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    sK1 != k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    sQ8_eqProxy(sK1,k5_relat_1(sK1,k6_relat_1(sK0))) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1) | ~spl9_3),
% 0.21/0.54    inference(resolution,[],[f107,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | sQ8_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_proxy_replacement,[],[f40,f57])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(rectify,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    spl9_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    $false | spl9_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f34])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ~v1_relat_1(sK1) | spl9_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f109,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl9_1),
% 0.21/0.54    inference(resolution,[],[f99,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | spl9_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ~spl9_1 | spl9_2 | spl9_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f95,f105,f101,f97])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f94,f34])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1)),
% 0.21/0.54    inference(resolution,[],[f60,f58])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sQ8_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_proxy_replacement,[],[f39,f57])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (27702)------------------------------
% 0.21/0.54  % (27702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27702)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (27702)Memory used [KB]: 10746
% 0.21/0.54  % (27702)Time elapsed: 0.136 s
% 0.21/0.54  % (27702)------------------------------
% 0.21/0.54  % (27702)------------------------------
% 0.21/0.54  % (27684)Success in time 0.171 s
%------------------------------------------------------------------------------
