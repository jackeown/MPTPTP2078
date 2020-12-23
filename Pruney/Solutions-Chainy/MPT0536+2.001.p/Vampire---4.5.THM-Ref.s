%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:06 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 338 expanded)
%              Number of leaves         :   21 ( 122 expanded)
%              Depth                    :   11
%              Number of atoms          :  437 (1781 expanded)
%              Number of equality atoms :   41 ( 244 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f886,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f190,f205,f339,f340,f348,f713,f719,f730,f741,f756,f757,f758,f794,f847,f881])).

fof(f881,plain,
    ( ~ spl10_1
    | ~ spl10_41
    | spl10_13
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f872,f791,f219,f738,f125])).

fof(f125,plain,
    ( spl10_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f738,plain,
    ( spl10_41
  <=> v1_relat_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f219,plain,
    ( spl10_13
  <=> r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f791,plain,
    ( spl10_45
  <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f872,plain,
    ( r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl10_45 ),
    inference(resolution,[],[f793,f74])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK6(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                    & r2_hidden(sK6(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f793,plain,
    ( r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f791])).

fof(f847,plain,
    ( ~ spl10_1
    | ~ spl10_39
    | ~ spl10_12
    | ~ spl10_11
    | spl10_44 ),
    inference(avatar_split_clause,[],[f841,f787,f201,f215,f710,f125])).

fof(f710,plain,
    ( spl10_39
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f215,plain,
    ( spl10_12
  <=> r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f201,plain,
    ( spl10_11
  <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f787,plain,
    ( spl10_44
  <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f841,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | spl10_44 ),
    inference(resolution,[],[f789,f72])).

fof(f72,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f789,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2))
    | spl10_44 ),
    inference(avatar_component_clause,[],[f787])).

fof(f794,plain,
    ( ~ spl10_44
    | spl10_45
    | spl10_9 ),
    inference(avatar_split_clause,[],[f777,f192,f791,f787])).

fof(f192,plain,
    ( spl10_9
  <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f777,plain,
    ( r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2))
    | spl10_9 ),
    inference(resolution,[],[f193,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f193,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | spl10_9 ),
    inference(avatar_component_clause,[],[f192])).

fof(f758,plain,
    ( ~ spl10_13
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f343,f196,f219])).

fof(f196,plain,
    ( spl10_10
  <=> r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f343,plain,
    ( ~ r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1)
    | ~ spl10_10 ),
    inference(resolution,[],[f198,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f44])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f198,plain,
    ( r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f757,plain,
    ( ~ spl10_1
    | ~ spl10_39
    | spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f702,f192,f201,f710,f125])).

fof(f702,plain,
    ( r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f329,f73])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f329,plain,
    ( r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2))
    | ~ spl10_9 ),
    inference(resolution,[],[f194,f77])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f44])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f194,plain,
    ( r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f192])).

fof(f756,plain,(
    spl10_41 ),
    inference(avatar_contradiction_clause,[],[f754])).

fof(f754,plain,
    ( $false
    | spl10_41 ),
    inference(resolution,[],[f740,f89])).

fof(f89,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k8_relat_1(k6_subset_1(sK0,sK1),sK2) != k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(k6_subset_1(X0,X1),X2) != k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & v1_relat_1(X2) )
   => ( k8_relat_1(k6_subset_1(sK0,sK1),sK2) != k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(k6_subset_1(X0,X1),X2) != k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).

fof(f740,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl10_41 ),
    inference(avatar_component_clause,[],[f738])).

fof(f741,plain,
    ( ~ spl10_1
    | ~ spl10_41
    | ~ spl10_13
    | ~ spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f731,f192,f201,f219,f738,f125])).

fof(f731,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f330,f72])).

fof(f330,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ spl10_9 ),
    inference(resolution,[],[f194,f76])).

fof(f730,plain,(
    spl10_39 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | spl10_39 ),
    inference(resolution,[],[f712,f89])).

fof(f712,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl10_39 ),
    inference(avatar_component_clause,[],[f710])).

fof(f719,plain,
    ( ~ spl10_12
    | spl10_13
    | spl10_10 ),
    inference(avatar_split_clause,[],[f209,f196,f219,f215])).

fof(f209,plain,
    ( r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1)
    | ~ r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0)
    | spl10_10 ),
    inference(resolution,[],[f197,f75])).

fof(f197,plain,
    ( ~ r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f713,plain,
    ( ~ spl10_1
    | ~ spl10_39
    | spl10_12
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f701,f192,f215,f710,f125])).

fof(f701,plain,
    ( r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f329,f74])).

fof(f348,plain,
    ( spl10_12
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f342,f196,f215])).

fof(f342,plain,
    ( r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0)
    | ~ spl10_10 ),
    inference(resolution,[],[f198,f77])).

fof(f340,plain,
    ( ~ spl10_6
    | spl10_9
    | spl10_10 ),
    inference(avatar_split_clause,[],[f260,f196,f192,f150])).

fof(f150,plain,
    ( spl10_6
  <=> v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f260,plain,
    ( r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) ),
    inference(resolution,[],[f103,f79])).

fof(f79,plain,(
    ~ sQ9_eqProxy(k8_relat_1(k6_subset_1(sK0,sK1),sK2),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f39,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f39,plain,(
    k8_relat_1(k6_subset_1(sK0,sK1),sK2) != k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,(
    ! [X24,X25] :
      ( sQ9_eqProxy(k8_relat_1(X24,sK2),X25)
      | r2_hidden(sK6(X24,sK2,X25),X24)
      | r2_hidden(k4_tarski(sK5(X24,sK2,X25),sK6(X24,sK2,X25)),X25)
      | ~ v1_relat_1(X25) ) ),
    inference(resolution,[],[f38,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f51,f78])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f339,plain,
    ( ~ spl10_6
    | spl10_9
    | spl10_11 ),
    inference(avatar_split_clause,[],[f290,f201,f192,f150])).

fof(f290,plain,
    ( r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2)
    | r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) ),
    inference(resolution,[],[f101,f79])).

fof(f101,plain,(
    ! [X21,X20] :
      ( sQ9_eqProxy(k8_relat_1(X20,sK2),X21)
      | r2_hidden(k4_tarski(sK5(X20,sK2,X21),sK6(X20,sK2,X21)),sK2)
      | r2_hidden(k4_tarski(sK5(X20,sK2,X21),sK6(X20,sK2,X21)),X21)
      | ~ v1_relat_1(X21) ) ),
    inference(resolution,[],[f38,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f52,f78])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f205,plain,
    ( ~ spl10_1
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f142,f201,f196,f192,f150,f125])).

fof(f142,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1))
    | ~ r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f79,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f53,f78])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f190,plain,(
    spl10_6 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl10_6 ),
    inference(resolution,[],[f185,f89])).

fof(f185,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl10_6 ),
    inference(resolution,[],[f152,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f181,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl10_1 ),
    inference(resolution,[],[f127,f38])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:54:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (26075)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.48  % (26056)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.48  % (26046)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.49  % (26064)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.49  % (26067)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.50  % (26055)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (26054)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (26051)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (26050)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (26073)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.51  % (26064)Refutation not found, incomplete strategy% (26064)------------------------------
% 0.19/0.51  % (26064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (26064)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (26064)Memory used [KB]: 10618
% 0.19/0.51  % (26064)Time elapsed: 0.112 s
% 0.19/0.51  % (26064)------------------------------
% 0.19/0.51  % (26064)------------------------------
% 0.19/0.51  % (26053)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (26063)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (26047)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (26072)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (26049)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (26048)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (26048)Refutation not found, incomplete strategy% (26048)------------------------------
% 0.19/0.52  % (26048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (26048)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (26048)Memory used [KB]: 10618
% 0.19/0.52  % (26048)Time elapsed: 0.122 s
% 0.19/0.52  % (26048)------------------------------
% 0.19/0.52  % (26048)------------------------------
% 0.19/0.52  % (26078)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (26062)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (26077)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (26071)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (26076)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.52  % (26071)Refutation not found, incomplete strategy% (26071)------------------------------
% 0.19/0.52  % (26071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (26071)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (26071)Memory used [KB]: 10746
% 0.19/0.52  % (26071)Time elapsed: 0.135 s
% 0.19/0.52  % (26071)------------------------------
% 0.19/0.52  % (26071)------------------------------
% 0.19/0.52  % (26070)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (26068)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (26069)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (26058)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (26061)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (26057)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.53  % (26060)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (26059)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (26074)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.71/0.59  % (26062)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.94/0.60  % SZS output start Proof for theBenchmark
% 1.94/0.60  fof(f886,plain,(
% 1.94/0.60    $false),
% 1.94/0.60    inference(avatar_sat_refutation,[],[f181,f190,f205,f339,f340,f348,f713,f719,f730,f741,f756,f757,f758,f794,f847,f881])).
% 1.94/0.61  fof(f881,plain,(
% 1.94/0.61    ~spl10_1 | ~spl10_41 | spl10_13 | ~spl10_45),
% 1.94/0.61    inference(avatar_split_clause,[],[f872,f791,f219,f738,f125])).
% 1.94/0.61  fof(f125,plain,(
% 1.94/0.61    spl10_1 <=> v1_relat_1(sK2)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.94/0.61  fof(f738,plain,(
% 1.94/0.61    spl10_41 <=> v1_relat_1(k8_relat_1(sK1,sK2))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 1.94/0.61  fof(f219,plain,(
% 1.94/0.61    spl10_13 <=> r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.94/0.61  fof(f791,plain,(
% 1.94/0.61    spl10_45 <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 1.94/0.61  fof(f872,plain,(
% 1.94/0.61    r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~spl10_45),
% 1.94/0.61    inference(resolution,[],[f793,f74])).
% 1.94/0.61  fof(f74,plain,(
% 1.94/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(equality_resolution,[],[f48])).
% 1.94/0.61  fof(f48,plain,(
% 1.94/0.61    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f28,plain,(
% 1.94/0.61    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.94/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f27])).
% 1.94/0.61  fof(f27,plain,(
% 1.94/0.61    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f26,plain,(
% 1.94/0.61    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.94/0.61    inference(rectify,[],[f25])).
% 1.94/0.61  fof(f25,plain,(
% 1.94/0.61    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.94/0.61    inference(flattening,[],[f24])).
% 1.94/0.61  fof(f24,plain,(
% 1.94/0.61    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.94/0.61    inference(nnf_transformation,[],[f16])).
% 1.94/0.61  fof(f16,plain,(
% 1.94/0.61    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.94/0.61    inference(ennf_transformation,[],[f4])).
% 1.94/0.61  fof(f4,axiom,(
% 1.94/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).
% 1.94/0.61  fof(f793,plain,(
% 1.94/0.61    r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2)) | ~spl10_45),
% 1.94/0.61    inference(avatar_component_clause,[],[f791])).
% 1.94/0.61  fof(f847,plain,(
% 1.94/0.61    ~spl10_1 | ~spl10_39 | ~spl10_12 | ~spl10_11 | spl10_44),
% 1.94/0.61    inference(avatar_split_clause,[],[f841,f787,f201,f215,f710,f125])).
% 1.94/0.61  fof(f710,plain,(
% 1.94/0.61    spl10_39 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 1.94/0.61  fof(f215,plain,(
% 1.94/0.61    spl10_12 <=> r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.94/0.61  fof(f201,plain,(
% 1.94/0.61    spl10_11 <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.94/0.61  fof(f787,plain,(
% 1.94/0.61    spl10_44 <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 1.94/0.61  fof(f841,plain,(
% 1.94/0.61    ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2) | ~r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | spl10_44),
% 1.94/0.61    inference(resolution,[],[f789,f72])).
% 1.94/0.61  fof(f72,plain,(
% 1.94/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(equality_resolution,[],[f50])).
% 1.94/0.61  fof(f50,plain,(
% 1.94/0.61    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f789,plain,(
% 1.94/0.61    ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2)) | spl10_44),
% 1.94/0.61    inference(avatar_component_clause,[],[f787])).
% 1.94/0.61  fof(f794,plain,(
% 1.94/0.61    ~spl10_44 | spl10_45 | spl10_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f777,f192,f791,f787])).
% 1.94/0.61  fof(f192,plain,(
% 1.94/0.61    spl10_9 <=> r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.94/0.61  fof(f777,plain,(
% 1.94/0.61    r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2)) | ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2)) | spl10_9),
% 1.94/0.61    inference(resolution,[],[f193,f75])).
% 1.94/0.61  fof(f75,plain,(
% 1.94/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.94/0.61    inference(equality_resolution,[],[f67])).
% 1.94/0.61  fof(f67,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k6_subset_1(X0,X1) != X2) )),
% 1.94/0.61    inference(definition_unfolding,[],[f59,f44])).
% 1.94/0.61  fof(f44,plain,(
% 1.94/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f3])).
% 1.94/0.61  fof(f3,axiom,(
% 1.94/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.94/0.61  fof(f59,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.61    inference(cnf_transformation,[],[f37])).
% 1.94/0.61  fof(f37,plain,(
% 1.94/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).
% 1.94/0.61  fof(f36,plain,(
% 1.94/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f35,plain,(
% 1.94/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/0.61    inference(rectify,[],[f34])).
% 1.94/0.61  fof(f34,plain,(
% 1.94/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/0.61    inference(flattening,[],[f33])).
% 1.94/0.61  fof(f33,plain,(
% 1.94/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/0.61    inference(nnf_transformation,[],[f2])).
% 1.94/0.61  fof(f2,axiom,(
% 1.94/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.94/0.61  fof(f193,plain,(
% 1.94/0.61    ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | spl10_9),
% 1.94/0.61    inference(avatar_component_clause,[],[f192])).
% 1.94/0.61  fof(f758,plain,(
% 1.94/0.61    ~spl10_13 | ~spl10_10),
% 1.94/0.61    inference(avatar_split_clause,[],[f343,f196,f219])).
% 1.94/0.61  fof(f196,plain,(
% 1.94/0.61    spl10_10 <=> r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.94/0.61  fof(f343,plain,(
% 1.94/0.61    ~r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1) | ~spl10_10),
% 1.94/0.61    inference(resolution,[],[f198,f76])).
% 1.94/0.61  fof(f76,plain,(
% 1.94/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 1.94/0.61    inference(equality_resolution,[],[f68])).
% 1.94/0.61  fof(f68,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.94/0.61    inference(definition_unfolding,[],[f58,f44])).
% 1.94/0.61  fof(f58,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.61    inference(cnf_transformation,[],[f37])).
% 1.94/0.61  fof(f198,plain,(
% 1.94/0.61    r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1)) | ~spl10_10),
% 1.94/0.61    inference(avatar_component_clause,[],[f196])).
% 1.94/0.61  fof(f757,plain,(
% 1.94/0.61    ~spl10_1 | ~spl10_39 | spl10_11 | ~spl10_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f702,f192,f201,f710,f125])).
% 1.94/0.61  fof(f702,plain,(
% 1.94/0.61    r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~spl10_9),
% 1.94/0.61    inference(resolution,[],[f329,f73])).
% 1.94/0.61  fof(f73,plain,(
% 1.94/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(equality_resolution,[],[f49])).
% 1.94/0.61  fof(f49,plain,(
% 1.94/0.61    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f329,plain,(
% 1.94/0.61    r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,sK2)) | ~spl10_9),
% 1.94/0.61    inference(resolution,[],[f194,f77])).
% 1.94/0.61  fof(f77,plain,(
% 1.94/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 1.94/0.61    inference(equality_resolution,[],[f69])).
% 1.94/0.61  fof(f69,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.94/0.61    inference(definition_unfolding,[],[f57,f44])).
% 1.94/0.61  fof(f57,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.61    inference(cnf_transformation,[],[f37])).
% 1.94/0.61  fof(f194,plain,(
% 1.94/0.61    r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | ~spl10_9),
% 1.94/0.61    inference(avatar_component_clause,[],[f192])).
% 1.94/0.61  fof(f756,plain,(
% 1.94/0.61    spl10_41),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f754])).
% 1.94/0.61  fof(f754,plain,(
% 1.94/0.61    $false | spl10_41),
% 1.94/0.61    inference(resolution,[],[f740,f89])).
% 1.94/0.61  fof(f89,plain,(
% 1.94/0.61    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 1.94/0.61    inference(resolution,[],[f38,f46])).
% 1.94/0.61  fof(f46,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f14])).
% 1.94/0.61  fof(f14,plain,(
% 1.94/0.61    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.94/0.61    inference(ennf_transformation,[],[f6])).
% 1.94/0.61  fof(f6,axiom,(
% 1.94/0.61    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.94/0.61  fof(f38,plain,(
% 1.94/0.61    v1_relat_1(sK2)),
% 1.94/0.61    inference(cnf_transformation,[],[f19])).
% 1.94/0.61  fof(f19,plain,(
% 1.94/0.61    k8_relat_1(k6_subset_1(sK0,sK1),sK2) != k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & v1_relat_1(sK2)),
% 1.94/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 1.94/0.61  fof(f18,plain,(
% 1.94/0.61    ? [X0,X1,X2] : (k8_relat_1(k6_subset_1(X0,X1),X2) != k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & v1_relat_1(X2)) => (k8_relat_1(k6_subset_1(sK0,sK1),sK2) != k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f11,plain,(
% 1.94/0.61    ? [X0,X1,X2] : (k8_relat_1(k6_subset_1(X0,X1),X2) != k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & v1_relat_1(X2))),
% 1.94/0.61    inference(ennf_transformation,[],[f10])).
% 1.94/0.61  fof(f10,negated_conjecture,(
% 1.94/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 1.94/0.61    inference(negated_conjecture,[],[f9])).
% 1.94/0.61  fof(f9,conjecture,(
% 1.94/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).
% 1.94/0.61  fof(f740,plain,(
% 1.94/0.61    ~v1_relat_1(k8_relat_1(sK1,sK2)) | spl10_41),
% 1.94/0.61    inference(avatar_component_clause,[],[f738])).
% 1.94/0.61  fof(f741,plain,(
% 1.94/0.61    ~spl10_1 | ~spl10_41 | ~spl10_13 | ~spl10_11 | ~spl10_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f731,f192,f201,f219,f738,f125])).
% 1.94/0.61  fof(f731,plain,(
% 1.94/0.61    ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2) | ~r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~spl10_9),
% 1.94/0.61    inference(resolution,[],[f330,f72])).
% 1.94/0.61  fof(f330,plain,(
% 1.94/0.61    ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2)) | ~spl10_9),
% 1.94/0.61    inference(resolution,[],[f194,f76])).
% 1.94/0.61  fof(f730,plain,(
% 1.94/0.61    spl10_39),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f728])).
% 1.94/0.61  fof(f728,plain,(
% 1.94/0.61    $false | spl10_39),
% 1.94/0.61    inference(resolution,[],[f712,f89])).
% 1.94/0.61  fof(f712,plain,(
% 1.94/0.61    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl10_39),
% 1.94/0.61    inference(avatar_component_clause,[],[f710])).
% 1.94/0.61  fof(f719,plain,(
% 1.94/0.61    ~spl10_12 | spl10_13 | spl10_10),
% 1.94/0.61    inference(avatar_split_clause,[],[f209,f196,f219,f215])).
% 1.94/0.61  fof(f209,plain,(
% 1.94/0.61    r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK1) | ~r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0) | spl10_10),
% 1.94/0.61    inference(resolution,[],[f197,f75])).
% 1.94/0.61  fof(f197,plain,(
% 1.94/0.61    ~r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1)) | spl10_10),
% 1.94/0.61    inference(avatar_component_clause,[],[f196])).
% 1.94/0.61  fof(f713,plain,(
% 1.94/0.61    ~spl10_1 | ~spl10_39 | spl10_12 | ~spl10_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f701,f192,f215,f710,f125])).
% 1.94/0.61  fof(f701,plain,(
% 1.94/0.61    r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~spl10_9),
% 1.94/0.61    inference(resolution,[],[f329,f74])).
% 1.94/0.61  fof(f348,plain,(
% 1.94/0.61    spl10_12 | ~spl10_10),
% 1.94/0.61    inference(avatar_split_clause,[],[f342,f196,f215])).
% 1.94/0.61  fof(f342,plain,(
% 1.94/0.61    r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK0) | ~spl10_10),
% 1.94/0.61    inference(resolution,[],[f198,f77])).
% 1.94/0.61  fof(f340,plain,(
% 1.94/0.61    ~spl10_6 | spl10_9 | spl10_10),
% 1.94/0.61    inference(avatar_split_clause,[],[f260,f196,f192,f150])).
% 1.94/0.61  fof(f150,plain,(
% 1.94/0.61    spl10_6 <=> v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.94/0.61  fof(f260,plain,(
% 1.94/0.61    r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1)) | r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | ~v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),
% 1.94/0.61    inference(resolution,[],[f103,f79])).
% 1.94/0.61  fof(f79,plain,(
% 1.94/0.61    ~sQ9_eqProxy(k8_relat_1(k6_subset_1(sK0,sK1),sK2),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),
% 1.94/0.61    inference(equality_proxy_replacement,[],[f39,f78])).
% 1.94/0.61  fof(f78,plain,(
% 1.94/0.61    ! [X1,X0] : (sQ9_eqProxy(X0,X1) <=> X0 = X1)),
% 1.94/0.61    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).
% 1.94/0.61  fof(f39,plain,(
% 1.94/0.61    k8_relat_1(k6_subset_1(sK0,sK1),sK2) != k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 1.94/0.61    inference(cnf_transformation,[],[f19])).
% 1.94/0.61  fof(f103,plain,(
% 1.94/0.61    ( ! [X24,X25] : (sQ9_eqProxy(k8_relat_1(X24,sK2),X25) | r2_hidden(sK6(X24,sK2,X25),X24) | r2_hidden(k4_tarski(sK5(X24,sK2,X25),sK6(X24,sK2,X25)),X25) | ~v1_relat_1(X25)) )),
% 1.94/0.61    inference(resolution,[],[f38,f84])).
% 1.94/0.61  fof(f84,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (sQ9_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(equality_proxy_replacement,[],[f51,f78])).
% 1.94/0.61  fof(f51,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f339,plain,(
% 1.94/0.61    ~spl10_6 | spl10_9 | spl10_11),
% 1.94/0.61    inference(avatar_split_clause,[],[f290,f201,f192,f150])).
% 1.94/0.61  fof(f290,plain,(
% 1.94/0.61    r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2) | r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | ~v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),
% 1.94/0.61    inference(resolution,[],[f101,f79])).
% 1.94/0.61  fof(f101,plain,(
% 1.94/0.61    ( ! [X21,X20] : (sQ9_eqProxy(k8_relat_1(X20,sK2),X21) | r2_hidden(k4_tarski(sK5(X20,sK2,X21),sK6(X20,sK2,X21)),sK2) | r2_hidden(k4_tarski(sK5(X20,sK2,X21),sK6(X20,sK2,X21)),X21) | ~v1_relat_1(X21)) )),
% 1.94/0.61    inference(resolution,[],[f38,f83])).
% 1.94/0.61  fof(f83,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (sQ9_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(equality_proxy_replacement,[],[f52,f78])).
% 1.94/0.61  fof(f52,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f205,plain,(
% 1.94/0.61    ~spl10_1 | ~spl10_6 | ~spl10_9 | ~spl10_10 | ~spl10_11),
% 1.94/0.61    inference(avatar_split_clause,[],[f142,f201,f196,f192,f150,f125])).
% 1.94/0.61  fof(f142,plain,(
% 1.94/0.61    ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),sK2) | ~r2_hidden(sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),k6_subset_1(sK0,sK1)) | ~r2_hidden(k4_tarski(sK5(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),sK6(k6_subset_1(sK0,sK1),sK2,k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)))),k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | ~v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | ~v1_relat_1(sK2)),
% 1.94/0.61    inference(resolution,[],[f79,f82])).
% 1.94/0.61  fof(f82,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (sQ9_eqProxy(k8_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(equality_proxy_replacement,[],[f53,f78])).
% 1.94/0.61  fof(f53,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f190,plain,(
% 1.94/0.61    spl10_6),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f188])).
% 1.94/0.61  fof(f188,plain,(
% 1.94/0.61    $false | spl10_6),
% 1.94/0.61    inference(resolution,[],[f185,f89])).
% 1.94/0.61  fof(f185,plain,(
% 1.94/0.61    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl10_6),
% 1.94/0.61    inference(resolution,[],[f152,f63])).
% 1.94/0.61  fof(f63,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.94/0.61    inference(definition_unfolding,[],[f45,f44])).
% 1.94/0.61  fof(f45,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f13])).
% 1.94/0.61  fof(f13,plain,(
% 1.94/0.61    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.94/0.61    inference(ennf_transformation,[],[f7])).
% 1.94/0.61  fof(f7,axiom,(
% 1.94/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 1.94/0.61  fof(f152,plain,(
% 1.94/0.61    ~v1_relat_1(k6_subset_1(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))) | spl10_6),
% 1.94/0.61    inference(avatar_component_clause,[],[f150])).
% 1.94/0.61  fof(f181,plain,(
% 1.94/0.61    spl10_1),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f180])).
% 1.94/0.61  fof(f180,plain,(
% 1.94/0.61    $false | spl10_1),
% 1.94/0.61    inference(resolution,[],[f127,f38])).
% 1.94/0.61  fof(f127,plain,(
% 1.94/0.61    ~v1_relat_1(sK2) | spl10_1),
% 1.94/0.61    inference(avatar_component_clause,[],[f125])).
% 1.94/0.61  % SZS output end Proof for theBenchmark
% 1.94/0.61  % (26062)------------------------------
% 1.94/0.61  % (26062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.61  % (26062)Termination reason: Refutation
% 1.94/0.61  
% 1.94/0.61  % (26062)Memory used [KB]: 7036
% 1.94/0.61  % (26062)Time elapsed: 0.166 s
% 1.94/0.61  % (26062)------------------------------
% 1.94/0.61  % (26062)------------------------------
% 1.94/0.61  % (26040)Success in time 0.268 s
%------------------------------------------------------------------------------
