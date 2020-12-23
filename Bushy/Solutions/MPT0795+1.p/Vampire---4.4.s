%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t47_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 522 expanded)
%              Number of leaves         :   42 ( 186 expanded)
%              Depth                    :   16
%              Number of atoms          :  614 (2190 expanded)
%              Number of equality atoms :   37 (  95 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f105,f116,f126,f181,f247,f266,f279,f295,f302,f317,f325,f327,f329,f331,f352,f365,f388,f403,f419,f430,f437,f439,f440,f454,f456,f460,f468,f471])).

fof(f471,plain,
    ( spl5_9
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f469,f464])).

fof(f464,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(duplicate_literal_removal,[],[f463])).

fof(f463,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f462,f442])).

fof(f442,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)) = sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f436,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t35_funct_1)).

fof(f436,plain,
    ( r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl5_36
  <=> r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f462,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f461,f332])).

fof(f332,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)) = sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f246,f87])).

fof(f246,plain,
    ( r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl5_12
  <=> r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f461,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1))),sK1)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f343,f436])).

fof(f343,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1))),sK1)
    | ~ r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f337,f180])).

fof(f180,plain,
    ( ~ sP0(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_9
  <=> ~ sP0(sK1,k6_relat_1(k3_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f337,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1))),sK1)
    | sP0(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f246,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
              & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
              & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
              | ~ r2_hidden(X6,k3_relat_1(X2))
              | ~ r2_hidden(X5,k3_relat_1(X2)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                & r2_hidden(X6,k3_relat_1(X2))
                & r2_hidden(X5,k3_relat_1(X2)) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
            | ~ r2_hidden(X4,k3_relat_1(X2))
            | ~ r2_hidden(X3,k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              & r2_hidden(X4,k3_relat_1(X2))
              & r2_hidden(X3,k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
            & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              | ~ r2_hidden(X4,k3_relat_1(X2))
              | ~ r2_hidden(X3,k3_relat_1(X2))
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
                & r2_hidden(X4,k3_relat_1(X2))
                & r2_hidden(X3,k3_relat_1(X2)) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
              | ~ r2_hidden(X6,k3_relat_1(X2))
              | ~ r2_hidden(X5,k3_relat_1(X2)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                & r2_hidden(X6,k3_relat_1(X2))
                & r2_hidden(X5,k3_relat_1(X2)) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X0)
        <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
            & r2_hidden(X4,k3_relat_1(X0))
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f469,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_20
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f301,f442])).

fof(f301,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl5_20
  <=> r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f468,plain,
    ( spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f466,f464])).

fof(f466,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f465,f442])).

fof(f465,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f342,f464])).

fof(f342,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f332,f188])).

fof(f188,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1))),sK1)
    | r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f74,f180])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f460,plain,
    ( spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f458,f240])).

fof(f240,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl5_10
  <=> r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f458,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f457,f442])).

fof(f457,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f441,f332])).

fof(f441,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1))),sK1)
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f180,f246,f240,f436,f75])).

fof(f456,plain,
    ( ~ spl5_10
    | spl5_21
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f452,f240])).

fof(f452,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f442,f298])).

fof(f298,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl5_21
  <=> ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f454,plain,
    ( ~ spl5_10
    | spl5_21
    | spl5_29
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_21
    | ~ spl5_29
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f451,f370])).

fof(f370,plain,
    ( m1_subset_1(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f240,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t1_subset)).

fof(f451,plain,
    ( ~ m1_subset_1(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_21
    | ~ spl5_29
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f442,f412])).

fof(f412,plain,
    ( ~ m1_subset_1(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_21
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f387,f298,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t2_subset)).

fof(f387,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f440,plain,
    ( spl5_36
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f368,f239,f96,f435])).

fof(f96,plain,
    ( spl5_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f368,plain,
    ( r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f97,f240,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t30_relat_1)).

fof(f97,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f96])).

fof(f439,plain,
    ( ~ spl5_0
    | ~ spl5_10
    | spl5_37 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f433,f368])).

fof(f433,plain,
    ( ~ r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl5_37
  <=> ~ r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f437,plain,
    ( spl5_10
    | spl5_36
    | spl5_9 ),
    inference(avatar_split_clause,[],[f184,f179,f435,f239])).

fof(f184,plain,
    ( r2_hidden(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f180,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f430,plain,
    ( spl5_34
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f404,f401,f428])).

fof(f428,plain,
    ( spl5_34
  <=> k1_funct_1(k6_relat_1(sK1),sK4(sK1)) = sK4(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f401,plain,
    ( spl5_30
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f404,plain,
    ( k1_funct_1(k6_relat_1(sK1),sK4(sK1)) = sK4(sK1)
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f402,f87])).

fof(f402,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f401])).

fof(f419,plain,
    ( ~ spl5_33
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f407,f401,f417])).

fof(f417,plain,
    ( spl5_33
  <=> ~ r2_hidden(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f407,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f402,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',antisymmetry_r2_hidden)).

fof(f403,plain,
    ( spl5_30
    | spl5_29 ),
    inference(avatar_split_clause,[],[f389,f386,f401])).

fof(f389,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f81,f387,f84])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',existence_m1_subset_1)).

fof(f388,plain,
    ( ~ spl5_29
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f373,f239,f386])).

fof(f373,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f240,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t7_boole)).

fof(f365,plain,
    ( spl5_26
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f280,f277,f363])).

fof(f363,plain,
    ( spl5_26
  <=> k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK4(k3_relat_1(sK1))) = sK4(k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f277,plain,
    ( spl5_16
  <=> r2_hidden(sK4(k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f280,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK4(k3_relat_1(sK1))) = sK4(k3_relat_1(sK1))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f278,f87])).

fof(f278,plain,
    ( r2_hidden(sK4(k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f277])).

fof(f352,plain,
    ( ~ spl5_25
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f335,f245,f350])).

fof(f350,plain,
    ( spl5_25
  <=> ~ r2_hidden(k3_relat_1(sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f335,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f246,f85])).

fof(f331,plain,
    ( ~ spl5_12
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f246,f319])).

fof(f319,plain,
    ( ~ r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_23 ),
    inference(resolution,[],[f316,f86])).

fof(f316,plain,
    ( ~ m1_subset_1(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl5_23
  <=> ~ m1_subset_1(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f329,plain,
    ( ~ spl5_0
    | spl5_9
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f321,f243])).

fof(f243,plain,
    ( ~ r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl5_13
  <=> ~ r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f321,plain,
    ( r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f180,f308,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f308,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_0
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f97,f243,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f327,plain,
    ( ~ spl5_0
    | spl5_9
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f322,f180])).

fof(f322,plain,
    ( sP0(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ spl5_0
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f243,f308,f73])).

fof(f325,plain,
    ( ~ spl5_0
    | spl5_9
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f180,f243,f308,f73])).

fof(f317,plain,
    ( ~ spl5_23
    | spl5_13
    | spl5_15 ),
    inference(avatar_split_clause,[],[f310,f264,f242,f315])).

fof(f264,plain,
    ( spl5_15
  <=> ~ v1_xboole_0(k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f310,plain,
    ( ~ m1_subset_1(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f265,f243,f84])).

fof(f265,plain,
    ( ~ v1_xboole_0(k3_relat_1(sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f264])).

fof(f302,plain,
    ( spl5_20
    | spl5_9
    | spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f259,f245,f236,f179,f300])).

fof(f236,plain,
    ( spl5_11
  <=> ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f259,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f258,f237])).

fof(f237,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f258,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f248,f188])).

fof(f248,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(sK1)),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)) = sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f246,f87])).

fof(f295,plain,
    ( ~ spl5_19
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f283,f277,f293])).

fof(f293,plain,
    ( spl5_19
  <=> ~ r2_hidden(k3_relat_1(sK1),sK4(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f283,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),sK4(k3_relat_1(sK1)))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f278,f85])).

fof(f279,plain,
    ( spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f271,f264,f277])).

fof(f271,plain,
    ( r2_hidden(sK4(k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f81,f265,f84])).

fof(f266,plain,
    ( ~ spl5_15
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f252,f245,f264])).

fof(f252,plain,
    ( ~ v1_xboole_0(k3_relat_1(sK1))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f246,f89])).

fof(f247,plain,
    ( spl5_10
    | spl5_12
    | spl5_9 ),
    inference(avatar_split_clause,[],[f183,f179,f245,f239])).

fof(f183,plain,
    ( r2_hidden(sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k6_relat_1(k3_relat_1(sK1)),sK1),sK3(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)),sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f180,f73])).

fof(f181,plain,
    ( ~ spl5_9
    | ~ spl5_0
    | spl5_7 ),
    inference(avatar_split_clause,[],[f169,f124,f96,f179])).

fof(f124,plain,
    ( spl5_7
  <=> ~ r3_wellord1(sK1,sK1,k6_relat_1(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f169,plain,
    ( ~ sP0(sK1,k6_relat_1(k3_relat_1(sK1)),sK1)
    | ~ spl5_0
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f97,f97,f59,f64,f62,f125,f65,f66,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ sP0(X1,X2,X0)
      | ~ v2_funct_1(X2)
      | k3_relat_1(X1) != k2_relat_1(X2)
      | k3_relat_1(X0) != k1_relat_1(X2)
      | r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ~ sP0(X1,X2,X0)
                  | ~ v2_funct_1(X2)
                  | k3_relat_1(X1) != k2_relat_1(X2)
                  | k3_relat_1(X0) != k1_relat_1(X2) )
                & ( ( sP0(X1,X2,X0)
                    & v2_funct_1(X2)
                    & k3_relat_1(X1) = k2_relat_1(X2)
                    & k3_relat_1(X0) = k1_relat_1(X2) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ~ sP0(X1,X2,X0)
                  | ~ v2_funct_1(X2)
                  | k3_relat_1(X1) != k2_relat_1(X2)
                  | k3_relat_1(X0) != k1_relat_1(X2) )
                & ( ( sP0(X1,X2,X0)
                    & v2_funct_1(X2)
                    & k3_relat_1(X1) = k2_relat_1(X2)
                    & k3_relat_1(X0) = k1_relat_1(X2) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( sP0(X1,X2,X0)
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f33,f43])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',d7_wellord1)).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t71_relat_1)).

fof(f65,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f125,plain,
    ( ~ r3_wellord1(sK1,sK1,k6_relat_1(k3_relat_1(sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',fc4_funct_1)).

fof(f64,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',fc3_funct_1)).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',dt_k6_relat_1)).

fof(f126,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f57,f124])).

fof(f57,plain,(
    ~ r3_wellord1(sK1,sK1,k6_relat_1(k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r3_wellord1(sK1,sK1,k6_relat_1(k3_relat_1(sK1)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r3_wellord1(sK1,sK1,k6_relat_1(k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t47_wellord1)).

fof(f116,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f106,f103,f114])).

fof(f114,plain,
    ( spl5_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f103,plain,
    ( spl5_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f104,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t6_boole)).

fof(f104,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f58,f103])).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',dt_o_0_0_xboole_0)).

fof(f98,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f56,f96])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
