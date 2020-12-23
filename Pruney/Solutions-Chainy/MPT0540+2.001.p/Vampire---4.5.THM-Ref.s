%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 286 expanded)
%              Number of leaves         :   19 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  456 (1583 expanded)
%              Number of equality atoms :   37 ( 183 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f712,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f126,f127,f147,f149,f170,f229,f234,f275,f286,f563,f605,f657,f693,f702,f703])).

fof(f703,plain,
    ( ~ spl8_17
    | ~ spl8_6
    | spl8_13
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f599,f114,f226,f110,f268])).

fof(f268,plain,
    ( spl8_17
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f110,plain,
    ( spl8_6
  <=> v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f226,plain,
    ( spl8_13
  <=> r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f114,plain,
    ( spl8_7
  <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f599,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl8_7 ),
    inference(resolution,[],[f116,f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f702,plain,
    ( ~ spl8_1
    | ~ spl8_17
    | spl8_14
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f650,f272,f231,f268,f87])).

fof(f87,plain,
    ( spl8_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f231,plain,
    ( spl8_14
  <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f272,plain,
    ( spl8_18
  <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f650,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f273,f41])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f273,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f272])).

fof(f693,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_14
    | spl8_9 ),
    inference(avatar_split_clause,[],[f688,f123,f231,f226,f106,f87])).

fof(f106,plain,
    ( spl8_5
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f123,plain,
    ( spl8_9
  <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f688,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | spl8_9 ),
    inference(resolution,[],[f124,f43])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f124,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f657,plain,
    ( ~ spl8_1
    | ~ spl8_17
    | spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f649,f272,f118,f268,f87])).

fof(f118,plain,
    ( spl8_8
  <=> r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f649,plain,
    ( r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f273,f42])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f605,plain,
    ( ~ spl8_17
    | ~ spl8_6
    | spl8_18
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f600,f114,f272,f110,f268])).

fof(f600,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl8_7 ),
    inference(resolution,[],[f116,f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f563,plain,
    ( ~ spl8_1
    | ~ spl8_17
    | ~ spl8_8
    | ~ spl8_14
    | spl8_18 ),
    inference(avatar_split_clause,[],[f558,f272,f231,f118,f268,f87])).

fof(f558,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl8_18 ),
    inference(resolution,[],[f274,f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f274,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f272])).

fof(f286,plain,(
    spl8_17 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl8_17 ),
    inference(resolution,[],[f270,f55])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f270,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f268])).

fof(f275,plain,
    ( ~ spl8_17
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_18
    | spl8_7 ),
    inference(avatar_split_clause,[],[f262,f114,f272,f226,f110,f268])).

fof(f262,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl8_7 ),
    inference(resolution,[],[f115,f43])).

fof(f115,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f234,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | spl8_14
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f220,f123,f231,f106,f87])).

fof(f220,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(resolution,[],[f125,f44])).

fof(f125,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f229,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | spl8_13
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f219,f123,f226,f106,f87])).

fof(f219,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(resolution,[],[f125,f45])).

fof(f170,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl8_6 ),
    inference(resolution,[],[f162,f55])).

fof(f162,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl8_6 ),
    inference(resolution,[],[f112,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f112,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f149,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f89,f24])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f147,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl8_5 ),
    inference(resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X1] : v1_relat_1(k8_relat_1(X1,sK2)) ),
    inference(resolution,[],[f24,f33])).

fof(f108,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f127,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f104,f123,f118,f114,f110,f106])).

fof(f104,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k7_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ sQ7_eqProxy(k7_relat_1(k8_relat_1(sK0,sK2),sK1),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f25,f46])).

fof(f25,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | spl8_9 ),
    inference(avatar_split_clause,[],[f103,f123,f114,f110,f106])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f30,f46])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f121,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f102,f118,f114,f110,f106])).

fof(f102,plain,
    ( r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f46])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21914)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (21919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (21919)Refutation not found, incomplete strategy% (21919)------------------------------
% 0.20/0.47  % (21919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (21919)Memory used [KB]: 1663
% 0.20/0.47  % (21919)Time elapsed: 0.003 s
% 0.20/0.47  % (21919)------------------------------
% 0.20/0.47  % (21919)------------------------------
% 0.20/0.47  % (21911)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (21922)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (21912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (21915)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (21910)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (21908)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (21925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (21916)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (21906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (21909)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (21907)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (21907)Refutation not found, incomplete strategy% (21907)------------------------------
% 0.20/0.50  % (21907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21907)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21907)Memory used [KB]: 10490
% 0.20/0.50  % (21907)Time elapsed: 0.092 s
% 0.20/0.50  % (21907)------------------------------
% 0.20/0.50  % (21907)------------------------------
% 0.20/0.50  % (21913)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (21918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (21926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (21926)Refutation not found, incomplete strategy% (21926)------------------------------
% 0.20/0.51  % (21926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21926)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21926)Memory used [KB]: 10490
% 0.20/0.51  % (21926)Time elapsed: 0.106 s
% 0.20/0.51  % (21926)------------------------------
% 0.20/0.51  % (21926)------------------------------
% 0.20/0.51  % (21924)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (21917)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (21921)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.53  % (21920)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.53  % (21923)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.54  % (21918)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f712,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f121,f126,f127,f147,f149,f170,f229,f234,f275,f286,f563,f605,f657,f693,f702,f703])).
% 0.20/0.54  fof(f703,plain,(
% 0.20/0.54    ~spl8_17 | ~spl8_6 | spl8_13 | ~spl8_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f599,f114,f226,f110,f268])).
% 0.20/0.54  fof(f268,plain,(
% 0.20/0.54    spl8_17 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    spl8_6 <=> v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    spl8_13 <=> r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    spl8_7 <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.54  fof(f599,plain,(
% 0.20/0.54    r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~spl8_7),
% 0.20/0.54    inference(resolution,[],[f116,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f21,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(rectify,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~spl8_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f114])).
% 0.20/0.54  fof(f702,plain,(
% 0.20/0.54    ~spl8_1 | ~spl8_17 | spl8_14 | ~spl8_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f650,f272,f231,f268,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    spl8_1 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.54  fof(f231,plain,(
% 0.20/0.54    spl8_14 <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.54  fof(f272,plain,(
% 0.20/0.54    spl8_18 <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.54  fof(f650,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl8_18),
% 0.20/0.54    inference(resolution,[],[f273,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(rectify,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.20/0.54  fof(f273,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) | ~spl8_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f272])).
% 0.20/0.54  fof(f693,plain,(
% 0.20/0.54    ~spl8_1 | ~spl8_5 | ~spl8_13 | ~spl8_14 | spl8_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f688,f123,f231,f226,f106,f87])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    spl8_5 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    spl8_9 <=> r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.54  fof(f688,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2) | ~r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | spl8_9),
% 0.20/0.54    inference(resolution,[],[f124,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2)) | spl8_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f123])).
% 0.20/0.54  fof(f657,plain,(
% 0.20/0.54    ~spl8_1 | ~spl8_17 | spl8_8 | ~spl8_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f649,f272,f118,f268,f87])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    spl8_8 <=> r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.54  fof(f649,plain,(
% 0.20/0.54    r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl8_18),
% 0.20/0.54    inference(resolution,[],[f273,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f605,plain,(
% 0.20/0.54    ~spl8_17 | ~spl8_6 | spl8_18 | ~spl8_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f600,f114,f272,f110,f268])).
% 0.20/0.54  fof(f600,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) | ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~spl8_7),
% 0.20/0.54    inference(resolution,[],[f116,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f563,plain,(
% 0.20/0.54    ~spl8_1 | ~spl8_17 | ~spl8_8 | ~spl8_14 | spl8_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f558,f272,f231,f118,f268,f87])).
% 0.20/0.54  fof(f558,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2) | ~r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl8_18),
% 0.20/0.54    inference(resolution,[],[f274,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) | spl8_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f272])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    spl8_17),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    $false | spl8_17),
% 0.20/0.54    inference(resolution,[],[f270,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.54    inference(resolution,[],[f24,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2)) => (k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f7,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f5])).
% 0.20/0.54  fof(f5,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.20/0.54  fof(f270,plain,(
% 0.20/0.54    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl8_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f268])).
% 0.20/0.54  fof(f275,plain,(
% 0.20/0.54    ~spl8_17 | ~spl8_6 | ~spl8_13 | ~spl8_18 | spl8_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f262,f114,f272,f226,f110,f268])).
% 0.20/0.54  fof(f262,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) | ~r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl8_7),
% 0.20/0.54    inference(resolution,[],[f115,f43])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | spl8_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f114])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    ~spl8_1 | ~spl8_5 | spl8_14 | ~spl8_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f220,f123,f231,f106,f87])).
% 0.20/0.54  fof(f220,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~spl8_9),
% 0.20/0.54    inference(resolution,[],[f125,f44])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2)) | ~spl8_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f123])).
% 0.20/0.54  fof(f229,plain,(
% 0.20/0.54    ~spl8_1 | ~spl8_5 | spl8_13 | ~spl8_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f219,f123,f226,f106,f87])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    r2_hidden(sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~spl8_9),
% 0.20/0.54    inference(resolution,[],[f125,f45])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    spl8_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.54  fof(f168,plain,(
% 0.20/0.54    $false | spl8_6),
% 0.20/0.54    inference(resolution,[],[f162,f55])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl8_6),
% 0.20/0.54    inference(resolution,[],[f112,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | spl8_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f110])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    spl8_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    $false | spl8_1),
% 0.20/0.54    inference(resolution,[],[f89,f24])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl8_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f87])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    spl8_5),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    $false | spl8_5),
% 0.20/0.54    inference(resolution,[],[f108,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK2))) )),
% 0.20/0.54    inference(resolution,[],[f24,f33])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl8_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f106])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f104,f123,f118,f114,f110,f106])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2)) | ~r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1) | ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f47,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sQ7_eqProxy(k7_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f31,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ~sQ7_eqProxy(k7_relat_1(k8_relat_1(sK0,sK2),sK1),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f25,f46])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ~spl8_5 | ~spl8_6 | spl8_7 | spl8_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f103,f123,f114,f110,f106])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f47,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sQ7_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f30,f46])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ~spl8_5 | ~spl8_6 | spl8_7 | spl8_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f102,f118,f114,f110,f106])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    r2_hidden(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1) | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK4(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f47,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sQ7_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f29,f46])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (21918)------------------------------
% 0.20/0.54  % (21918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21918)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (21918)Memory used [KB]: 6652
% 0.20/0.54  % (21918)Time elapsed: 0.110 s
% 0.20/0.54  % (21918)------------------------------
% 0.20/0.54  % (21918)------------------------------
% 0.20/0.54  % (21905)Success in time 0.183 s
%------------------------------------------------------------------------------
