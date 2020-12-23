%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 195 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  358 ( 667 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f67,f76,f91,f97,f100,f108,f113,f126,f130,f161,f204,f214,f259])).

fof(f259,plain,
    ( ~ spl8_6
    | spl8_9
    | ~ spl8_12
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f254,f212,f128,f106,f89])).

fof(f89,plain,
    ( spl8_6
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f106,plain,
    ( spl8_9
  <=> r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f128,plain,
    ( spl8_12
  <=> r2_hidden(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f212,plain,
    ( spl8_26
  <=> r2_hidden(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f254,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1)
    | r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ spl8_26 ),
    inference(resolution,[],[f239,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f239,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X1,sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_26 ),
    inference(resolution,[],[f213,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f213,plain,
    ( r2_hidden(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK2)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl8_26
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f205,f202,f212])).

fof(f202,plain,
    ( spl8_25
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f205,plain,
    ( r2_hidden(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK2)
    | ~ spl8_25 ),
    inference(resolution,[],[f203,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f203,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( spl8_25
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f199,f159,f57,f202])).

fof(f57,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f159,plain,
    ( spl8_18
  <=> ! [X1] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),X1)
        | ~ r1_tarski(sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f199,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2))
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(resolution,[],[f194,f58])).

fof(f58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f194,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),X1) )
    | ~ spl8_18 ),
    inference(resolution,[],[f160,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f160,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK3,X1)
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),X1) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( ~ spl8_7
    | spl8_18
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f151,f124,f159,f95])).

fof(f95,plain,
    ( spl8_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f124,plain,
    ( spl8_11
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f151,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),X1)
        | ~ r1_tarski(sK3,X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_11 ),
    inference(resolution,[],[f125,f32])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f125,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f130,plain,
    ( ~ spl8_7
    | spl8_12
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f119,f111,f128,f95])).

fof(f111,plain,
    ( spl8_10
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f119,plain,
    ( r2_hidden(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(resolution,[],[f112,f60])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK6(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                    & r2_hidden(sK6(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k7_relat_1(sK3,sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f126,plain,
    ( ~ spl8_7
    | spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f118,f111,f124,f95])).

fof(f118,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(resolution,[],[f112,f61])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( spl8_10
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f109,f74,f57,f111])).

fof(f74,plain,
    ( spl8_5
  <=> r2_hidden(k4_tarski(sK4(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2))),k5_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k7_relat_1(sK3,sK1))
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f75,f81])).

fof(f81,plain,
    ( ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl8_2 ),
    inference(resolution,[],[f45,f58])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK4(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2))),k5_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f108,plain,
    ( ~ spl8_9
    | ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f86,f65,f57,f106])).

fof(f65,plain,
    ( spl8_3
  <=> r1_tarski(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f86,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl8_2
    | spl8_3 ),
    inference(superposition,[],[f66,f81])).

fof(f66,plain,
    ( ~ r1_tarski(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f100,plain,
    ( ~ spl8_2
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl8_2
    | spl8_7 ),
    inference(subsumption_resolution,[],[f58,f98])).

fof(f98,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_7 ),
    inference(resolution,[],[f96,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f96,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( ~ spl8_7
    | spl8_6 ),
    inference(avatar_split_clause,[],[f92,f89,f95])).

fof(f92,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_6 ),
    inference(resolution,[],[f90,f41])).

fof(f90,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( ~ spl8_6
    | ~ spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f85,f71,f57,f89])).

fof(f71,plain,
    ( spl8_4
  <=> v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f85,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ spl8_2
    | spl8_4 ),
    inference(superposition,[],[f72,f81])).

fof(f72,plain,
    ( ~ v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f76,plain,
    ( ~ spl8_4
    | spl8_5
    | spl8_3 ),
    inference(avatar_split_clause,[],[f69,f65,f74,f71])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK4(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2))),k5_relset_1(sK0,sK2,sK3,sK1))
    | ~ v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1))
    | spl8_3 ),
    inference(resolution,[],[f33,f66])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,
    ( ~ spl8_3
    | spl8_1 ),
    inference(avatar_split_clause,[],[f63,f53,f65])).

fof(f53,plain,
    ( spl8_1
  <=> m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f63,plain,
    ( ~ r1_tarski(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | spl8_1 ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f55,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
