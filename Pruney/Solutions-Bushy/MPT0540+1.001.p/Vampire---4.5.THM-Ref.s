%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0540+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
