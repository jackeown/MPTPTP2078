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
% DateTime   : Thu Dec  3 12:48:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 106 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  234 ( 422 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f60,f63,f71,f86,f90])).

fof(f90,plain,
    ( ~ spl6_3
    | spl6_1
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f87,f84,f37,f55])).

fof(f55,plain,
    ( spl6_3
  <=> v1_relat_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f37,plain,
    ( spl6_1
  <=> r1_tarski(k8_relat_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( spl6_8
  <=> r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f87,plain,
    ( r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f85,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( ~ spl6_2
    | spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f77,f69,f84,f41])).

fof(f41,plain,
    ( spl6_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f69,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f26,f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK5(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
                    & r2_hidden(sK5(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( ~ spl6_3
    | spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f66,f58,f69,f55])).

fof(f58,plain,
    ( spl6_4
  <=> ! [X0] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK1),X0)
        | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f66,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(resolution,[],[f59,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK1),X0)
        | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),X0) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f61,f55,f41])).

fof(f61,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_3 ),
    inference(resolution,[],[f56,f26])).

fof(f56,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f60,plain,
    ( ~ spl6_3
    | spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f53,f37,f58,f55])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK1),X0)
        | ~ v1_relat_1(k8_relat_1(sK0,sK1))
        | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),X0) )
    | spl6_1 ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f23,f24])).

fof(f23,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k8_relat_1(X0,X1),X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k8_relat_1(X0,X1),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f39,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (26431)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (26438)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (26440)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (26430)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (26442)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (26434)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (26432)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (26430)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f39,f43,f60,f63,f71,f86,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~spl6_3 | spl6_1 | ~spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f84,f37,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl6_3 <=> v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    spl6_1 <=> r1_tarski(k8_relat_1(sK0,sK1),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl6_8 <=> r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f85,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~spl6_2 | spl6_8 | ~spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f69,f84,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl6_2 <=> v1_relat_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl6_5 <=> r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1) | ~v1_relat_1(sK1) | ~spl6_5),
% 0.22/0.50    inference(resolution,[],[f70,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X5,X6),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(global_subsumption,[],[f26,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(rectify,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1)) | ~spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~spl6_3 | spl6_5 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f66,f58,f69,f55])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl6_4 <=> ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK1),X0) | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1)) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | ~spl6_4),
% 0.22/0.50    inference(resolution,[],[f59,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0) | ~v1_relat_1(X0) | r1_tarski(X0,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f25,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK1),X0) | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),X0)) ) | ~spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ~spl6_2 | spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f55,f41])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ~v1_relat_1(sK1) | spl6_3),
% 0.22/0.50    inference(resolution,[],[f56,f26])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~v1_relat_1(k8_relat_1(sK0,sK1)) | spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~spl6_3 | spl6_4 | spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f37,f58,f55])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK1),X0) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),X0)) ) | spl6_1),
% 0.22/0.50    inference(resolution,[],[f49,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f37])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f23,f24])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f41])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) & v1_relat_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : (~r1_tarski(k8_relat_1(X0,X1),X1) & v1_relat_1(X1)) => (~r1_tarski(k8_relat_1(sK0,sK1),sK1) & v1_relat_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0,X1] : (~r1_tarski(k8_relat_1(X0,X1),X1) & v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f37])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ~r1_tarski(k8_relat_1(sK0,sK1),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (26430)------------------------------
% 0.22/0.50  % (26430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26430)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (26430)Memory used [KB]: 10618
% 0.22/0.50  % (26430)Time elapsed: 0.064 s
% 0.22/0.50  % (26430)------------------------------
% 0.22/0.50  % (26430)------------------------------
% 0.22/0.50  % (26439)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (26423)Success in time 0.14 s
%------------------------------------------------------------------------------
