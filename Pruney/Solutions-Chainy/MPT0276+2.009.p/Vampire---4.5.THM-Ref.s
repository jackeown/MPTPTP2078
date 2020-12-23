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
% DateTime   : Thu Dec  3 12:41:29 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 503 expanded)
%              Number of leaves         :   45 ( 175 expanded)
%              Depth                    :   18
%              Number of atoms          :  592 (2783 expanded)
%              Number of equality atoms :  197 (1109 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1697,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f109,f131,f140,f161,f175,f181,f190,f222,f229,f238,f251,f271,f293,f378,f443,f458,f459,f461,f571,f661,f662,f912,f914,f921,f1691,f1695,f1696])).

fof(f1696,plain,
    ( sK1 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1695,plain,
    ( sK0 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1691,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f1670])).

fof(f1670,plain,
    ( $false
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f58,f1637,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1637,plain,
    ( ! [X0] : r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),X0)
    | ~ spl6_5 ),
    inference(resolution,[],[f1607,f104])).

fof(f104,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_5
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1607,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X16,k1_xboole_0)
      | r2_hidden(X16,X15) ) ),
    inference(condensation,[],[f1599])).

fof(f1599,plain,(
    ! [X17,X15,X16] :
      ( ~ r2_hidden(X16,k1_xboole_0)
      | r2_hidden(X16,X15)
      | r2_hidden(X17,X15) ) ),
    inference(superposition,[],[f64,f1569])).

fof(f1569,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f1086,f64])).

fof(f1086,plain,(
    ! [X21,X20] :
      ( r2_hidden(X20,k5_xboole_0(X21,k3_xboole_0(X21,X21)))
      | k1_xboole_0 = k5_xboole_0(X21,k3_xboole_0(X21,X21)) ) ),
    inference(superposition,[],[f60,f452])).

fof(f452,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k2_tarski(X1,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f88,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_tarski(X2,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ) ),
    inference(resolution,[],[f50,f64])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f88,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X5),X4)
      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_tarski(X5,X5)
      | k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f50,f63])).

fof(f60,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f921,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f918])).

fof(f918,plain,
    ( $false
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f60,f373])).

fof(f373,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl6_26
  <=> r2_hidden(sK0,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f914,plain,
    ( sK1 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f912,plain,
    ( spl6_16
    | ~ spl6_28
    | ~ spl6_30
    | spl6_3
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f864,f268,f76,f562,f436,f195])).

fof(f195,plain,
    ( spl6_16
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f436,plain,
    ( spl6_28
  <=> r2_hidden(sK1,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f562,plain,
    ( spl6_30
  <=> r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f76,plain,
    ( spl6_3
  <=> k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f268,plain,
    ( spl6_23
  <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f864,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | r2_hidden(sK1,sK2)
    | spl6_3
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f863,f270])).

fof(f270,plain,
    ( sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f268])).

fof(f863,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | spl6_3
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f862,f270])).

fof(f862,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | spl6_3
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f207,f270])).

fof(f207,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | spl6_3 ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK1) != X1
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),sK2)
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),k2_tarski(sK0,sK1))
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),X1) )
    | spl6_3 ),
    inference(superposition,[],[f78,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK1,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f662,plain,
    ( sK0 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f661,plain,
    ( spl6_36
    | spl6_37
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f638,f128,f658,f654])).

fof(f654,plain,
    ( spl6_36
  <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f658,plain,
    ( spl6_37
  <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f128,plain,
    ( spl6_7
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f638,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl6_7 ),
    inference(resolution,[],[f130,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f130,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f571,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl6_30 ),
    inference(unit_resulting_resolution,[],[f58,f564])).

fof(f564,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f562])).

fof(f461,plain,
    ( sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f459,plain,
    ( sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f458,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f58,f377])).

fof(f377,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl6_27
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f443,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl6_28 ),
    inference(unit_resulting_resolution,[],[f58,f438])).

fof(f438,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f436])).

fof(f378,plain,
    ( spl6_18
    | ~ spl6_26
    | ~ spl6_27
    | spl6_4
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f357,f226,f81,f375,f371,f209])).

fof(f209,plain,
    ( spl6_18
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f81,plain,
    ( spl6_4
  <=> k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f226,plain,
    ( spl6_20
  <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f357,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | r2_hidden(sK0,sK2)
    | spl6_4
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f356,f228])).

fof(f228,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f226])).

fof(f356,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f355,f228])).

fof(f355,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f193,f228])).

fof(f193,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2)
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,
    ( ! [X0] :
        ( k2_tarski(sK0,sK0) != X0
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),sK2)
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),X0) )
    | spl6_4 ),
    inference(superposition,[],[f83,f51])).

fof(f83,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK0,sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f293,plain,
    ( spl6_23
    | spl6_24
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f288,f248,f290,f268])).

fof(f290,plain,
    ( spl6_24
  <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f248,plain,
    ( spl6_22
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f288,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | ~ spl6_22 ),
    inference(resolution,[],[f250,f61])).

fof(f250,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f271,plain,
    ( spl6_23
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f266,f154,f268])).

fof(f154,plain,
    ( spl6_10
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f266,plain,
    ( sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))
    | ~ spl6_10 ),
    inference(resolution,[],[f156,f61])).

fof(f156,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f251,plain,
    ( spl6_10
    | spl6_22
    | spl6_3 ),
    inference(avatar_split_clause,[],[f172,f76,f248,f154])).

fof(f172,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | spl6_3 ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK1) != X1
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),k2_tarski(sK0,sK1))
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),X1) )
    | spl6_3 ),
    inference(superposition,[],[f78,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f238,plain,
    ( spl6_21
    | spl6_20
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f233,f219,f226,f235])).

fof(f235,plain,
    ( spl6_21
  <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f219,plain,
    ( spl6_19
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f233,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | ~ spl6_19 ),
    inference(resolution,[],[f221,f61])).

fof(f221,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f219])).

fof(f229,plain,
    ( spl6_20
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f224,f133,f226])).

fof(f133,plain,
    ( spl6_8
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f224,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f135,f61])).

fof(f135,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f222,plain,
    ( spl6_8
    | spl6_19
    | spl6_4 ),
    inference(avatar_split_clause,[],[f171,f81,f219,f133])).

fof(f171,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( k2_tarski(sK0,sK0) != X0
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),X0) )
    | spl6_4 ),
    inference(superposition,[],[f83,f53])).

fof(f190,plain,
    ( spl6_14
    | spl6_15
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f179,f163,f187,f183])).

fof(f183,plain,
    ( spl6_14
  <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f187,plain,
    ( spl6_15
  <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f163,plain,
    ( spl6_12
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f179,plain,
    ( sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))
    | ~ spl6_12 ),
    inference(resolution,[],[f165,f61])).

fof(f165,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f181,plain,
    ( spl6_2
    | ~ spl6_12
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl6_2
    | ~ spl6_12
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f169,f165,f73,f165,f51])).

fof(f73,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_2
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f169,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_13
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f175,plain,
    ( spl6_12
    | spl6_2 ),
    inference(avatar_split_clause,[],[f174,f71,f163])).

fof(f174,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | spl6_2 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,
    ( ! [X2] :
        ( k2_tarski(sK0,sK1) != X2
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1))
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X2),X2) )
    | spl6_2 ),
    inference(superposition,[],[f73,f53])).

fof(f161,plain,
    ( spl6_10
    | ~ spl6_11
    | spl6_3 ),
    inference(avatar_split_clause,[],[f121,f76,f158,f154])).

fof(f158,plain,
    ( spl6_11
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f121,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2)
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | spl6_3 ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK1) != X1
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),sK2)
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),X1) )
    | spl6_3 ),
    inference(superposition,[],[f78,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f140,plain,
    ( spl6_8
    | ~ spl6_9
    | spl6_4 ),
    inference(avatar_split_clause,[],[f120,f81,f137,f133])).

fof(f137,plain,
    ( spl6_9
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f120,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2)
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl6_4 ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,
    ( ! [X0] :
        ( k2_tarski(sK0,sK0) != X0
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),sK2)
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),X0) )
    | spl6_4 ),
    inference(superposition,[],[f83,f52])).

fof(f131,plain,
    ( spl6_5
    | spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f126,f66,f128,f102])).

fof(f66,plain,
    ( spl6_1
  <=> k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f126,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),k2_tarski(sK0,sK1))
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),X3) )
    | spl6_1 ),
    inference(superposition,[],[f68,f53])).

fof(f68,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f109,plain,
    ( spl6_5
    | ~ spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f100,f66,f106,f102])).

fof(f106,plain,
    ( spl6_6
  <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f100,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),sK2)
        | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),X3) )
    | spl6_1 ),
    inference(superposition,[],[f68,f52])).

fof(f84,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f47,f81])).

fof(f47,plain,(
    k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f26,f44,f31])).

fof(f26,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f79,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f46,f76])).

fof(f46,plain,(
    k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f27,f44,f31])).

fof(f27,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f45,f71])).

fof(f45,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f28,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f48,f66])).

fof(f48,plain,(
    k1_xboole_0 != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f25,f44])).

fof(f25,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15271)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (15294)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (15275)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (15300)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (15300)Refutation not found, incomplete strategy% (15300)------------------------------
% 0.21/0.55  % (15300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15300)Memory used [KB]: 1663
% 0.21/0.55  % (15300)Time elapsed: 0.148 s
% 0.21/0.55  % (15300)------------------------------
% 0.21/0.55  % (15300)------------------------------
% 0.21/0.56  % (15284)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (15286)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (15298)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (15276)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (15282)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.57  % (15278)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (15279)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (15292)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (15293)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.64/0.58  % (15285)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.64/0.58  % (15285)Refutation not found, incomplete strategy% (15285)------------------------------
% 1.64/0.58  % (15285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (15285)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (15285)Memory used [KB]: 1663
% 1.64/0.58  % (15285)Time elapsed: 0.092 s
% 1.64/0.58  % (15285)------------------------------
% 1.64/0.58  % (15285)------------------------------
% 1.64/0.58  % (15290)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.64/0.59  % (15277)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.59  % (15298)Refutation not found, incomplete strategy% (15298)------------------------------
% 1.64/0.59  % (15298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (15298)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (15298)Memory used [KB]: 6140
% 1.64/0.59  % (15298)Time elapsed: 0.180 s
% 1.64/0.59  % (15298)------------------------------
% 1.64/0.59  % (15298)------------------------------
% 1.82/0.59  % (15272)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.82/0.59  % (15272)Refutation not found, incomplete strategy% (15272)------------------------------
% 1.82/0.59  % (15272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.59  % (15272)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.59  
% 1.82/0.59  % (15272)Memory used [KB]: 1663
% 1.82/0.59  % (15272)Time elapsed: 0.171 s
% 1.82/0.59  % (15272)------------------------------
% 1.82/0.59  % (15272)------------------------------
% 1.82/0.60  % (15274)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.82/0.60  % (15281)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.82/0.60  % (15280)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.82/0.60  % (15299)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.82/0.61  % (15295)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.82/0.61  % (15287)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.82/0.61  % (15287)Refutation not found, incomplete strategy% (15287)------------------------------
% 1.82/0.61  % (15287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (15295)Refutation not found, incomplete strategy% (15295)------------------------------
% 1.82/0.61  % (15295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (15287)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  % (15291)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.82/0.61  
% 1.82/0.61  % (15287)Memory used [KB]: 10618
% 1.82/0.61  % (15287)Time elapsed: 0.188 s
% 1.82/0.61  % (15287)------------------------------
% 1.82/0.61  % (15287)------------------------------
% 1.82/0.61  % (15295)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (15295)Memory used [KB]: 10618
% 1.82/0.61  % (15295)Time elapsed: 0.195 s
% 1.82/0.61  % (15295)------------------------------
% 1.82/0.61  % (15295)------------------------------
% 1.82/0.61  % (15283)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.82/0.62  % (15289)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.82/0.62  % (15288)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.82/0.62  % (15273)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.11/0.63  % (15297)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.11/0.63  % (15297)Refutation not found, incomplete strategy% (15297)------------------------------
% 2.11/0.63  % (15297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.63  % (15297)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.63  
% 2.11/0.63  % (15297)Memory used [KB]: 6140
% 2.11/0.63  % (15297)Time elapsed: 0.208 s
% 2.11/0.63  % (15297)------------------------------
% 2.11/0.63  % (15297)------------------------------
% 2.11/0.64  % (15289)Refutation not found, incomplete strategy% (15289)------------------------------
% 2.11/0.64  % (15289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (15296)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.11/0.64  % (15289)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (15289)Memory used [KB]: 1663
% 2.11/0.64  % (15289)Time elapsed: 0.209 s
% 2.11/0.64  % (15289)------------------------------
% 2.11/0.64  % (15289)------------------------------
% 2.11/0.64  % (15288)Refutation not found, incomplete strategy% (15288)------------------------------
% 2.11/0.64  % (15288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (15288)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (15288)Memory used [KB]: 1663
% 2.11/0.64  % (15288)Time elapsed: 0.217 s
% 2.11/0.64  % (15288)------------------------------
% 2.11/0.64  % (15288)------------------------------
% 2.53/0.71  % (15294)Refutation found. Thanks to Tanya!
% 2.53/0.71  % SZS status Theorem for theBenchmark
% 2.53/0.71  % SZS output start Proof for theBenchmark
% 2.53/0.71  fof(f1697,plain,(
% 2.53/0.71    $false),
% 2.53/0.71    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f109,f131,f140,f161,f175,f181,f190,f222,f229,f238,f251,f271,f293,f378,f443,f458,f459,f461,f571,f661,f662,f912,f914,f921,f1691,f1695,f1696])).
% 2.53/0.71  fof(f1696,plain,(
% 2.53/0.71    sK1 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK1,sK2)),
% 2.53/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.53/0.71  fof(f1695,plain,(
% 2.53/0.71    sK0 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK0,sK2)),
% 2.53/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.53/0.71  fof(f1691,plain,(
% 2.53/0.71    ~spl6_5),
% 2.53/0.71    inference(avatar_contradiction_clause,[],[f1670])).
% 2.53/0.71  fof(f1670,plain,(
% 2.53/0.71    $false | ~spl6_5),
% 2.53/0.71    inference(unit_resulting_resolution,[],[f58,f1637,f63])).
% 2.53/0.71  fof(f63,plain,(
% 2.53/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.53/0.71    inference(equality_resolution,[],[f55])).
% 2.53/0.71  fof(f55,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.53/0.71    inference(definition_unfolding,[],[f39,f44])).
% 2.53/0.71  fof(f44,plain,(
% 2.53/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.53/0.71    inference(cnf_transformation,[],[f2])).
% 2.53/0.71  fof(f2,axiom,(
% 2.53/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.53/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.53/0.71  fof(f39,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.53/0.71    inference(cnf_transformation,[],[f24])).
% 2.53/0.71  fof(f24,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.53/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 2.53/0.71  fof(f23,plain,(
% 2.53/0.71    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.53/0.71    introduced(choice_axiom,[])).
% 2.53/0.71  fof(f22,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.53/0.71    inference(rectify,[],[f21])).
% 2.53/0.71  fof(f21,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.53/0.71    inference(flattening,[],[f20])).
% 2.53/0.71  fof(f20,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.53/0.71    inference(nnf_transformation,[],[f1])).
% 2.53/0.71  fof(f1,axiom,(
% 2.53/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.53/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.53/0.71  fof(f1637,plain,(
% 2.53/0.71    ( ! [X0] : (r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),X0)) ) | ~spl6_5),
% 2.53/0.71    inference(resolution,[],[f1607,f104])).
% 2.53/0.71  fof(f104,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl6_5),
% 2.53/0.71    inference(avatar_component_clause,[],[f102])).
% 2.53/0.71  fof(f102,plain,(
% 2.53/0.71    spl6_5 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.53/0.71  fof(f1607,plain,(
% 2.53/0.71    ( ! [X15,X16] : (~r2_hidden(X16,k1_xboole_0) | r2_hidden(X16,X15)) )),
% 2.53/0.71    inference(condensation,[],[f1599])).
% 2.53/0.71  fof(f1599,plain,(
% 2.53/0.71    ( ! [X17,X15,X16] : (~r2_hidden(X16,k1_xboole_0) | r2_hidden(X16,X15) | r2_hidden(X17,X15)) )),
% 2.53/0.71    inference(superposition,[],[f64,f1569])).
% 2.53/0.71  fof(f1569,plain,(
% 2.53/0.71    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 2.53/0.71    inference(resolution,[],[f1086,f64])).
% 2.53/0.71  fof(f1086,plain,(
% 2.53/0.71    ( ! [X21,X20] : (r2_hidden(X20,k5_xboole_0(X21,k3_xboole_0(X21,X21))) | k1_xboole_0 = k5_xboole_0(X21,k3_xboole_0(X21,X21))) )),
% 2.53/0.71    inference(superposition,[],[f60,f452])).
% 2.53/0.71  fof(f452,plain,(
% 2.53/0.71    ( ! [X0,X1] : (k2_tarski(X1,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.53/0.71    inference(duplicate_literal_removal,[],[f447])).
% 2.53/0.71  fof(f447,plain,(
% 2.53/0.71    ( ! [X0,X1] : (k2_tarski(X1,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k2_tarski(X1,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.53/0.71    inference(resolution,[],[f88,f87])).
% 2.53/0.71  fof(f87,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (r2_hidden(sK3(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_tarski(X2,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.53/0.71    inference(resolution,[],[f50,f64])).
% 2.53/0.71  fof(f50,plain,(
% 2.53/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 2.53/0.71    inference(definition_unfolding,[],[f29,f31])).
% 2.53/0.71  fof(f31,plain,(
% 2.53/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.53/0.71    inference(cnf_transformation,[],[f4])).
% 2.53/0.71  fof(f4,axiom,(
% 2.53/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.53/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.53/0.71  fof(f29,plain,(
% 2.53/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.53/0.71    inference(cnf_transformation,[],[f14])).
% 2.53/0.71  fof(f14,plain,(
% 2.53/0.71    ! [X0,X1] : ((sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.53/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f13])).
% 2.53/0.71  fof(f13,plain,(
% 2.53/0.71    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)))),
% 2.53/0.71    introduced(choice_axiom,[])).
% 2.53/0.71  fof(f10,plain,(
% 2.53/0.71    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.53/0.71    inference(ennf_transformation,[],[f6])).
% 2.53/0.71  fof(f6,axiom,(
% 2.53/0.71    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.53/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 2.53/0.71  fof(f88,plain,(
% 2.53/0.71    ( ! [X4,X5,X3] : (~r2_hidden(sK3(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X5),X4) | k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_tarski(X5,X5) | k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.53/0.71    inference(resolution,[],[f50,f63])).
% 2.53/0.71  fof(f60,plain,(
% 2.53/0.71    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.53/0.71    inference(equality_resolution,[],[f59])).
% 2.53/0.71  fof(f59,plain,(
% 2.53/0.71    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.53/0.71    inference(equality_resolution,[],[f33])).
% 2.53/0.71  fof(f33,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.53/0.71    inference(cnf_transformation,[],[f19])).
% 2.53/0.71  fof(f19,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 2.53/0.71  fof(f18,plain,(
% 2.53/0.71    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.53/0.71    introduced(choice_axiom,[])).
% 2.53/0.71  fof(f17,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/0.71    inference(rectify,[],[f16])).
% 2.53/0.71  fof(f16,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/0.71    inference(flattening,[],[f15])).
% 2.53/0.71  fof(f15,plain,(
% 2.53/0.71    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/0.71    inference(nnf_transformation,[],[f3])).
% 2.53/0.71  fof(f3,axiom,(
% 2.53/0.71    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.53/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.53/0.71  fof(f64,plain,(
% 2.53/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 2.53/0.71    inference(equality_resolution,[],[f56])).
% 2.53/0.71  fof(f56,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.53/0.71    inference(definition_unfolding,[],[f38,f44])).
% 2.53/0.71  fof(f38,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.53/0.71    inference(cnf_transformation,[],[f24])).
% 2.53/0.71  fof(f58,plain,(
% 2.53/0.71    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.53/0.71    inference(equality_resolution,[],[f57])).
% 2.53/0.71  fof(f57,plain,(
% 2.53/0.71    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.53/0.71    inference(equality_resolution,[],[f34])).
% 2.53/0.71  fof(f34,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.53/0.71    inference(cnf_transformation,[],[f19])).
% 2.53/0.71  fof(f921,plain,(
% 2.53/0.71    spl6_26),
% 2.53/0.71    inference(avatar_contradiction_clause,[],[f918])).
% 2.53/0.71  fof(f918,plain,(
% 2.53/0.71    $false | spl6_26),
% 2.53/0.71    inference(unit_resulting_resolution,[],[f60,f373])).
% 2.53/0.71  fof(f373,plain,(
% 2.53/0.71    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | spl6_26),
% 2.53/0.71    inference(avatar_component_clause,[],[f371])).
% 2.53/0.71  fof(f371,plain,(
% 2.53/0.71    spl6_26 <=> r2_hidden(sK0,k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.53/0.71  fof(f914,plain,(
% 2.53/0.71    sK1 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)),
% 2.53/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.53/0.71  fof(f912,plain,(
% 2.53/0.71    spl6_16 | ~spl6_28 | ~spl6_30 | spl6_3 | ~spl6_23),
% 2.53/0.71    inference(avatar_split_clause,[],[f864,f268,f76,f562,f436,f195])).
% 2.53/0.71  fof(f195,plain,(
% 2.53/0.71    spl6_16 <=> r2_hidden(sK1,sK2)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.53/0.71  fof(f436,plain,(
% 2.53/0.71    spl6_28 <=> r2_hidden(sK1,k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.53/0.71  fof(f562,plain,(
% 2.53/0.71    spl6_30 <=> r2_hidden(sK1,k2_tarski(sK1,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.53/0.71  fof(f76,plain,(
% 2.53/0.71    spl6_3 <=> k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) = k2_tarski(sK1,sK1)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.53/0.71  fof(f268,plain,(
% 2.53/0.71    spl6_23 <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.53/0.71  fof(f864,plain,(
% 2.53/0.71    ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | r2_hidden(sK1,sK2) | (spl6_3 | ~spl6_23)),
% 2.53/0.71    inference(forward_demodulation,[],[f863,f270])).
% 2.53/0.71  fof(f270,plain,(
% 2.53/0.71    sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | ~spl6_23),
% 2.53/0.71    inference(avatar_component_clause,[],[f268])).
% 2.53/0.71  fof(f863,plain,(
% 2.53/0.71    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | r2_hidden(sK1,sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | (spl6_3 | ~spl6_23)),
% 2.53/0.71    inference(forward_demodulation,[],[f862,f270])).
% 2.53/0.71  fof(f862,plain,(
% 2.53/0.71    r2_hidden(sK1,sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | (spl6_3 | ~spl6_23)),
% 2.53/0.71    inference(forward_demodulation,[],[f207,f270])).
% 2.53/0.71  fof(f207,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | spl6_3),
% 2.53/0.71    inference(equality_resolution,[],[f145])).
% 2.53/0.71  fof(f145,plain,(
% 2.53/0.71    ( ! [X1] : (k2_tarski(sK1,sK1) != X1 | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),X1)) ) | spl6_3),
% 2.53/0.71    inference(superposition,[],[f78,f51])).
% 2.53/0.71  fof(f51,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.53/0.71    inference(definition_unfolding,[],[f43,f44])).
% 2.53/0.71  fof(f43,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.53/0.71    inference(cnf_transformation,[],[f24])).
% 2.53/0.71  fof(f78,plain,(
% 2.53/0.71    k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK1,sK1) | spl6_3),
% 2.53/0.71    inference(avatar_component_clause,[],[f76])).
% 2.53/0.71  fof(f662,plain,(
% 2.53/0.71    sK0 != sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)),
% 2.53/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.53/0.71  fof(f661,plain,(
% 2.53/0.71    spl6_36 | spl6_37 | ~spl6_7),
% 2.53/0.71    inference(avatar_split_clause,[],[f638,f128,f658,f654])).
% 2.53/0.71  fof(f654,plain,(
% 2.53/0.71    spl6_36 <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 2.53/0.71  fof(f658,plain,(
% 2.53/0.71    spl6_37 <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.53/0.71  fof(f128,plain,(
% 2.53/0.71    spl6_7 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.53/0.71  fof(f638,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl6_7),
% 2.53/0.71    inference(resolution,[],[f130,f61])).
% 2.53/0.71  fof(f61,plain,(
% 2.53/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.53/0.71    inference(equality_resolution,[],[f32])).
% 2.53/0.71  fof(f32,plain,(
% 2.53/0.71    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.53/0.71    inference(cnf_transformation,[],[f19])).
% 2.53/0.71  fof(f130,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | ~spl6_7),
% 2.53/0.71    inference(avatar_component_clause,[],[f128])).
% 2.53/0.71  fof(f571,plain,(
% 2.53/0.71    spl6_30),
% 2.53/0.71    inference(avatar_contradiction_clause,[],[f566])).
% 2.53/0.71  fof(f566,plain,(
% 2.53/0.71    $false | spl6_30),
% 2.53/0.71    inference(unit_resulting_resolution,[],[f58,f564])).
% 2.53/0.71  fof(f564,plain,(
% 2.53/0.71    ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | spl6_30),
% 2.53/0.71    inference(avatar_component_clause,[],[f562])).
% 2.53/0.71  fof(f461,plain,(
% 2.53/0.71    sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | sK0 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)),
% 2.53/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.53/0.71  fof(f459,plain,(
% 2.53/0.71    sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | sK1 != sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2)),
% 2.53/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.53/0.71  fof(f458,plain,(
% 2.53/0.71    spl6_27),
% 2.53/0.71    inference(avatar_contradiction_clause,[],[f453])).
% 2.53/0.71  fof(f453,plain,(
% 2.53/0.71    $false | spl6_27),
% 2.53/0.71    inference(unit_resulting_resolution,[],[f58,f377])).
% 2.53/0.71  fof(f377,plain,(
% 2.53/0.71    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl6_27),
% 2.53/0.71    inference(avatar_component_clause,[],[f375])).
% 2.53/0.71  fof(f375,plain,(
% 2.53/0.71    spl6_27 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.53/0.71  fof(f443,plain,(
% 2.53/0.71    spl6_28),
% 2.53/0.71    inference(avatar_contradiction_clause,[],[f440])).
% 2.53/0.71  fof(f440,plain,(
% 2.53/0.71    $false | spl6_28),
% 2.53/0.71    inference(unit_resulting_resolution,[],[f58,f438])).
% 2.53/0.71  fof(f438,plain,(
% 2.53/0.71    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | spl6_28),
% 2.53/0.71    inference(avatar_component_clause,[],[f436])).
% 2.53/0.71  fof(f378,plain,(
% 2.53/0.71    spl6_18 | ~spl6_26 | ~spl6_27 | spl6_4 | ~spl6_20),
% 2.53/0.71    inference(avatar_split_clause,[],[f357,f226,f81,f375,f371,f209])).
% 2.53/0.71  fof(f209,plain,(
% 2.53/0.71    spl6_18 <=> r2_hidden(sK0,sK2)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.53/0.71  fof(f81,plain,(
% 2.53/0.71    spl6_4 <=> k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) = k2_tarski(sK0,sK0)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.53/0.71  fof(f226,plain,(
% 2.53/0.71    spl6_20 <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.53/0.71  fof(f357,plain,(
% 2.53/0.71    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | r2_hidden(sK0,sK2) | (spl6_4 | ~spl6_20)),
% 2.53/0.71    inference(forward_demodulation,[],[f356,f228])).
% 2.53/0.71  fof(f228,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | ~spl6_20),
% 2.53/0.71    inference(avatar_component_clause,[],[f226])).
% 2.53/0.71  fof(f356,plain,(
% 2.53/0.71    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | (spl6_4 | ~spl6_20)),
% 2.53/0.71    inference(forward_demodulation,[],[f355,f228])).
% 2.53/0.71  fof(f355,plain,(
% 2.53/0.71    r2_hidden(sK0,sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | (spl6_4 | ~spl6_20)),
% 2.53/0.71    inference(forward_demodulation,[],[f193,f228])).
% 2.53/0.71  fof(f193,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl6_4),
% 2.53/0.71    inference(equality_resolution,[],[f144])).
% 2.53/0.71  fof(f144,plain,(
% 2.53/0.71    ( ! [X0] : (k2_tarski(sK0,sK0) != X0 | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),sK2) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),X0)) ) | spl6_4),
% 2.53/0.71    inference(superposition,[],[f83,f51])).
% 2.53/0.71  fof(f83,plain,(
% 2.53/0.71    k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK0,sK0) | spl6_4),
% 2.53/0.71    inference(avatar_component_clause,[],[f81])).
% 2.53/0.71  fof(f293,plain,(
% 2.53/0.71    spl6_23 | spl6_24 | ~spl6_22),
% 2.53/0.71    inference(avatar_split_clause,[],[f288,f248,f290,f268])).
% 2.53/0.71  fof(f290,plain,(
% 2.53/0.71    spl6_24 <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.53/0.71  fof(f248,plain,(
% 2.53/0.71    spl6_22 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.53/0.71  fof(f288,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | ~spl6_22),
% 2.53/0.71    inference(resolution,[],[f250,f61])).
% 2.53/0.71  fof(f250,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1)) | ~spl6_22),
% 2.53/0.71    inference(avatar_component_clause,[],[f248])).
% 2.53/0.71  fof(f271,plain,(
% 2.53/0.71    spl6_23 | ~spl6_10),
% 2.53/0.71    inference(avatar_split_clause,[],[f266,f154,f268])).
% 2.53/0.71  fof(f154,plain,(
% 2.53/0.71    spl6_10 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.53/0.71  fof(f266,plain,(
% 2.53/0.71    sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | ~spl6_10),
% 2.53/0.71    inference(duplicate_literal_removal,[],[f265])).
% 2.53/0.71  fof(f265,plain,(
% 2.53/0.71    sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)) | ~spl6_10),
% 2.53/0.71    inference(resolution,[],[f156,f61])).
% 2.53/0.71  fof(f156,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | ~spl6_10),
% 2.53/0.71    inference(avatar_component_clause,[],[f154])).
% 2.53/0.71  fof(f251,plain,(
% 2.53/0.71    spl6_10 | spl6_22 | spl6_3),
% 2.53/0.71    inference(avatar_split_clause,[],[f172,f76,f248,f154])).
% 2.53/0.71  fof(f172,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | spl6_3),
% 2.53/0.71    inference(equality_resolution,[],[f113])).
% 2.53/0.71  fof(f113,plain,(
% 2.53/0.71    ( ! [X1] : (k2_tarski(sK1,sK1) != X1 | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),X1)) ) | spl6_3),
% 2.53/0.71    inference(superposition,[],[f78,f53])).
% 2.53/0.71  fof(f53,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.53/0.71    inference(definition_unfolding,[],[f41,f44])).
% 2.53/0.71  fof(f41,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.53/0.71    inference(cnf_transformation,[],[f24])).
% 2.53/0.71  fof(f238,plain,(
% 2.53/0.71    spl6_21 | spl6_20 | ~spl6_19),
% 2.53/0.71    inference(avatar_split_clause,[],[f233,f219,f226,f235])).
% 2.53/0.71  fof(f235,plain,(
% 2.53/0.71    spl6_21 <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.53/0.71  fof(f219,plain,(
% 2.53/0.71    spl6_19 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.53/0.71  fof(f233,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | ~spl6_19),
% 2.53/0.71    inference(resolution,[],[f221,f61])).
% 2.53/0.71  fof(f221,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) | ~spl6_19),
% 2.53/0.71    inference(avatar_component_clause,[],[f219])).
% 2.53/0.71  fof(f229,plain,(
% 2.53/0.71    spl6_20 | ~spl6_8),
% 2.53/0.71    inference(avatar_split_clause,[],[f224,f133,f226])).
% 2.53/0.71  fof(f133,plain,(
% 2.53/0.71    spl6_8 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.53/0.71  fof(f224,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | ~spl6_8),
% 2.53/0.71    inference(duplicate_literal_removal,[],[f223])).
% 2.53/0.71  fof(f223,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)) | ~spl6_8),
% 2.53/0.71    inference(resolution,[],[f135,f61])).
% 2.53/0.71  fof(f135,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~spl6_8),
% 2.53/0.71    inference(avatar_component_clause,[],[f133])).
% 2.53/0.71  fof(f222,plain,(
% 2.53/0.71    spl6_8 | spl6_19 | spl6_4),
% 2.53/0.71    inference(avatar_split_clause,[],[f171,f81,f219,f133])).
% 2.53/0.71  fof(f171,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl6_4),
% 2.53/0.71    inference(equality_resolution,[],[f112])).
% 2.53/0.71  fof(f112,plain,(
% 2.53/0.71    ( ! [X0] : (k2_tarski(sK0,sK0) != X0 | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),X0)) ) | spl6_4),
% 2.53/0.71    inference(superposition,[],[f83,f53])).
% 2.53/0.71  fof(f190,plain,(
% 2.53/0.71    spl6_14 | spl6_15 | ~spl6_12),
% 2.53/0.71    inference(avatar_split_clause,[],[f179,f163,f187,f183])).
% 2.53/0.71  fof(f183,plain,(
% 2.53/0.71    spl6_14 <=> sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.53/0.71  fof(f187,plain,(
% 2.53/0.71    spl6_15 <=> sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.53/0.71  fof(f163,plain,(
% 2.53/0.71    spl6_12 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.53/0.71  fof(f179,plain,(
% 2.53/0.71    sK0 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | sK1 = sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)) | ~spl6_12),
% 2.53/0.71    inference(resolution,[],[f165,f61])).
% 2.53/0.71  fof(f165,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~spl6_12),
% 2.53/0.71    inference(avatar_component_clause,[],[f163])).
% 2.53/0.71  fof(f181,plain,(
% 2.53/0.71    spl6_2 | ~spl6_12 | spl6_13),
% 2.53/0.71    inference(avatar_contradiction_clause,[],[f178])).
% 2.53/0.71  fof(f178,plain,(
% 2.53/0.71    $false | (spl6_2 | ~spl6_12 | spl6_13)),
% 2.53/0.71    inference(unit_resulting_resolution,[],[f169,f165,f73,f165,f51])).
% 2.53/0.71  fof(f73,plain,(
% 2.53/0.71    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl6_2),
% 2.53/0.71    inference(avatar_component_clause,[],[f71])).
% 2.53/0.71  fof(f71,plain,(
% 2.53/0.71    spl6_2 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.53/0.71  fof(f169,plain,(
% 2.53/0.71    ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2) | spl6_13),
% 2.53/0.71    inference(avatar_component_clause,[],[f167])).
% 2.53/0.71  fof(f167,plain,(
% 2.53/0.71    spl6_13 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),sK2)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.53/0.71  fof(f175,plain,(
% 2.53/0.71    spl6_12 | spl6_2),
% 2.53/0.71    inference(avatar_split_clause,[],[f174,f71,f163])).
% 2.53/0.71  fof(f174,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | spl6_2),
% 2.53/0.71    inference(duplicate_literal_removal,[],[f173])).
% 2.53/0.71  fof(f173,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | spl6_2),
% 2.53/0.71    inference(equality_resolution,[],[f114])).
% 2.53/0.71  fof(f114,plain,(
% 2.53/0.71    ( ! [X2] : (k2_tarski(sK0,sK1) != X2 | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X2),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X2),X2)) ) | spl6_2),
% 2.53/0.71    inference(superposition,[],[f73,f53])).
% 2.53/0.71  fof(f161,plain,(
% 2.53/0.71    spl6_10 | ~spl6_11 | spl6_3),
% 2.53/0.71    inference(avatar_split_clause,[],[f121,f76,f158,f154])).
% 2.53/0.71  fof(f158,plain,(
% 2.53/0.71    spl6_11 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.53/0.71  fof(f121,plain,(
% 2.53/0.71    ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | spl6_3),
% 2.53/0.71    inference(equality_resolution,[],[f94])).
% 2.53/0.71  fof(f94,plain,(
% 2.53/0.71    ( ! [X1] : (k2_tarski(sK1,sK1) != X1 | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X1),X1)) ) | spl6_3),
% 2.53/0.71    inference(superposition,[],[f78,f52])).
% 2.53/0.71  fof(f52,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.53/0.71    inference(definition_unfolding,[],[f42,f44])).
% 2.53/0.71  fof(f42,plain,(
% 2.53/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.53/0.71    inference(cnf_transformation,[],[f24])).
% 2.53/0.71  fof(f140,plain,(
% 2.53/0.71    spl6_8 | ~spl6_9 | spl6_4),
% 2.53/0.71    inference(avatar_split_clause,[],[f120,f81,f137,f133])).
% 2.53/0.71  fof(f137,plain,(
% 2.53/0.71    spl6_9 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.53/0.71  fof(f120,plain,(
% 2.53/0.71    ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl6_4),
% 2.53/0.71    inference(equality_resolution,[],[f93])).
% 2.53/0.71  fof(f93,plain,(
% 2.53/0.71    ( ! [X0] : (k2_tarski(sK0,sK0) != X0 | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X0),X0)) ) | spl6_4),
% 2.53/0.71    inference(superposition,[],[f83,f52])).
% 2.53/0.71  fof(f131,plain,(
% 2.53/0.71    spl6_5 | spl6_7 | spl6_1),
% 2.53/0.71    inference(avatar_split_clause,[],[f126,f66,f128,f102])).
% 2.53/0.71  fof(f66,plain,(
% 2.53/0.71    spl6_1 <=> k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.53/0.71  fof(f126,plain,(
% 2.53/0.71    r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_1),
% 2.53/0.71    inference(equality_resolution,[],[f115])).
% 2.53/0.71  fof(f115,plain,(
% 2.53/0.71    ( ! [X3] : (k1_xboole_0 != X3 | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),X3)) ) | spl6_1),
% 2.53/0.71    inference(superposition,[],[f68,f53])).
% 2.53/0.71  fof(f68,plain,(
% 2.53/0.71    k1_xboole_0 != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl6_1),
% 2.53/0.71    inference(avatar_component_clause,[],[f66])).
% 2.53/0.71  fof(f109,plain,(
% 2.53/0.71    spl6_5 | ~spl6_6 | spl6_1),
% 2.53/0.71    inference(avatar_split_clause,[],[f100,f66,f106,f102])).
% 2.53/0.71  fof(f106,plain,(
% 2.53/0.71    spl6_6 <=> r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)),
% 2.53/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.53/0.71  fof(f100,plain,(
% 2.53/0.71    ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_1),
% 2.53/0.71    inference(equality_resolution,[],[f96])).
% 2.53/0.71  fof(f96,plain,(
% 2.53/0.71    ( ! [X3] : (k1_xboole_0 != X3 | ~r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),sK2) | r2_hidden(sK5(k2_tarski(sK0,sK1),sK2,X3),X3)) ) | spl6_1),
% 2.53/0.71    inference(superposition,[],[f68,f52])).
% 2.53/0.71  fof(f84,plain,(
% 2.53/0.71    ~spl6_4),
% 2.53/0.71    inference(avatar_split_clause,[],[f47,f81])).
% 2.53/0.71  fof(f47,plain,(
% 2.53/0.71    k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK0,sK0)),
% 2.53/0.71    inference(definition_unfolding,[],[f26,f44,f31])).
% 2.53/0.71  fof(f26,plain,(
% 2.53/0.71    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 2.53/0.71    inference(cnf_transformation,[],[f12])).
% 2.53/0.71  fof(f12,plain,(
% 2.53/0.71    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.53/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 2.53/0.71  fof(f11,plain,(
% 2.53/0.71    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.53/0.71    introduced(choice_axiom,[])).
% 2.53/0.71  fof(f9,plain,(
% 2.53/0.71    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.53/0.71    inference(ennf_transformation,[],[f8])).
% 2.53/0.71  fof(f8,negated_conjecture,(
% 2.53/0.71    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.53/0.71    inference(negated_conjecture,[],[f7])).
% 2.53/0.71  fof(f7,conjecture,(
% 2.53/0.71    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.53/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 2.53/0.71  fof(f79,plain,(
% 2.53/0.71    ~spl6_3),
% 2.53/0.71    inference(avatar_split_clause,[],[f46,f76])).
% 2.53/0.71  fof(f46,plain,(
% 2.53/0.71    k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) != k2_tarski(sK1,sK1)),
% 2.53/0.71    inference(definition_unfolding,[],[f27,f44,f31])).
% 2.53/0.71  fof(f27,plain,(
% 2.53/0.71    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 2.53/0.71    inference(cnf_transformation,[],[f12])).
% 2.53/0.71  fof(f74,plain,(
% 2.53/0.71    ~spl6_2),
% 2.53/0.71    inference(avatar_split_clause,[],[f45,f71])).
% 2.53/0.71  fof(f45,plain,(
% 2.53/0.71    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.53/0.71    inference(definition_unfolding,[],[f28,f44])).
% 2.53/0.71  fof(f28,plain,(
% 2.53/0.71    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.53/0.71    inference(cnf_transformation,[],[f12])).
% 2.53/0.71  fof(f69,plain,(
% 2.53/0.71    ~spl6_1),
% 2.53/0.71    inference(avatar_split_clause,[],[f48,f66])).
% 2.53/0.71  fof(f48,plain,(
% 2.53/0.71    k1_xboole_0 != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.53/0.71    inference(definition_unfolding,[],[f25,f44])).
% 2.53/0.71  fof(f25,plain,(
% 2.53/0.71    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.53/0.71    inference(cnf_transformation,[],[f12])).
% 2.53/0.71  % SZS output end Proof for theBenchmark
% 2.53/0.71  % (15294)------------------------------
% 2.53/0.71  % (15294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.53/0.71  % (15294)Termination reason: Refutation
% 2.53/0.71  
% 2.53/0.71  % (15294)Memory used [KB]: 11897
% 2.53/0.71  % (15294)Time elapsed: 0.278 s
% 2.53/0.71  % (15294)------------------------------
% 2.53/0.71  % (15294)------------------------------
% 2.53/0.71  % (15270)Success in time 0.343 s
%------------------------------------------------------------------------------
