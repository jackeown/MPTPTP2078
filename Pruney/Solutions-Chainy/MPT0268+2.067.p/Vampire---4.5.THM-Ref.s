%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:45 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 198 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  274 ( 773 expanded)
%              Number of equality atoms :   49 ( 155 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f109,f407,f412,f447])).

fof(f447,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f443,f425])).

fof(f425,plain,
    ( r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f60,f68])).

fof(f68,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f443,plain,
    ( ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f415,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f415,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f73,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f73,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f412,plain,
    ( ~ spl5_4
    | spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f168,f71,f67,f106])).

fof(f106,plain,
    ( spl5_4
  <=> r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f168,plain,
    ( ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f78,f98,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f98,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f97,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f97,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0)
    | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0)
    | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(superposition,[],[f85,f59])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f85,plain,
    ( ! [X0] :
        ( sK0 != k5_xboole_0(sK0,X0)
        | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),sK0)
        | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f69,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f78,plain,
    ( r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f72,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f72,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f407,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f382,f399])).

fof(f399,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),X0)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f391,f59])).

fof(f391,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f60,f175,f44])).

fof(f175,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f104,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_3
  <=> r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f382,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f104,f175,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,
    ( spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f100,f67,f106,f102])).

fof(f100,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(superposition,[],[f86,f59])).

fof(f86,plain,
    ( ! [X1] :
        ( sK0 != k5_xboole_0(sK0,X1)
        | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),k2_enumset1(sK1,sK1,sK1,sK1))
        | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1) )
    | spl5_1 ),
    inference(superposition,[],[f69,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f58,f71,f67])).

fof(f58,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f34,f41,f56])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f74,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f57,f71,f67])).

fof(f57,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f35,f41,f56])).

fof(f35,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (27339)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.50  % (27323)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (27332)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (27323)Refutation not found, incomplete strategy% (27323)------------------------------
% 0.22/0.50  % (27323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27323)Memory used [KB]: 10618
% 0.22/0.50  % (27323)Time elapsed: 0.086 s
% 0.22/0.50  % (27323)------------------------------
% 0.22/0.50  % (27323)------------------------------
% 0.22/0.51  % (27316)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (27331)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (27322)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (27321)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (27324)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (27328)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (27338)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (27340)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (27337)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (27329)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (27344)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (27330)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (27315)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (27330)Refutation not found, incomplete strategy% (27330)------------------------------
% 0.22/0.53  % (27330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27317)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (27330)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27330)Memory used [KB]: 6140
% 0.22/0.53  % (27330)Time elapsed: 0.002 s
% 0.22/0.53  % (27330)------------------------------
% 0.22/0.53  % (27330)------------------------------
% 0.22/0.53  % (27320)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (27317)Refutation not found, incomplete strategy% (27317)------------------------------
% 1.30/0.54  % (27317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (27317)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (27317)Memory used [KB]: 10618
% 1.30/0.54  % (27317)Time elapsed: 0.108 s
% 1.30/0.54  % (27317)------------------------------
% 1.30/0.54  % (27317)------------------------------
% 1.30/0.54  % (27326)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (27325)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.54  % (27318)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (27325)Refutation not found, incomplete strategy% (27325)------------------------------
% 1.30/0.54  % (27325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (27325)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (27325)Memory used [KB]: 10618
% 1.30/0.54  % (27325)Time elapsed: 0.102 s
% 1.30/0.54  % (27325)------------------------------
% 1.30/0.54  % (27325)------------------------------
% 1.30/0.54  % (27341)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (27335)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (27333)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.55  % (27337)Refutation not found, incomplete strategy% (27337)------------------------------
% 1.30/0.55  % (27337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (27337)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (27337)Memory used [KB]: 10618
% 1.30/0.55  % (27337)Time elapsed: 0.137 s
% 1.30/0.55  % (27337)------------------------------
% 1.30/0.55  % (27337)------------------------------
% 1.30/0.55  % (27336)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.55  % (27343)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.55  % (27334)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (27326)Refutation not found, incomplete strategy% (27326)------------------------------
% 1.45/0.55  % (27326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (27326)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  % (27319)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  
% 1.45/0.55  % (27326)Memory used [KB]: 10618
% 1.45/0.55  % (27326)Time elapsed: 0.155 s
% 1.45/0.55  % (27326)------------------------------
% 1.45/0.55  % (27326)------------------------------
% 1.45/0.56  % (27342)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.56  % (27327)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.59  % (27341)Refutation found. Thanks to Tanya!
% 1.45/0.59  % SZS status Theorem for theBenchmark
% 1.45/0.59  % SZS output start Proof for theBenchmark
% 1.45/0.59  fof(f448,plain,(
% 1.45/0.59    $false),
% 1.45/0.59    inference(avatar_sat_refutation,[],[f74,f75,f109,f407,f412,f447])).
% 1.45/0.59  fof(f447,plain,(
% 1.45/0.59    ~spl5_1 | ~spl5_2),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f446])).
% 1.45/0.59  fof(f446,plain,(
% 1.45/0.59    $false | (~spl5_1 | ~spl5_2)),
% 1.45/0.59    inference(subsumption_resolution,[],[f443,f425])).
% 1.45/0.59  fof(f425,plain,(
% 1.45/0.59    r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_1),
% 1.45/0.59    inference(superposition,[],[f60,f68])).
% 1.45/0.59  fof(f68,plain,(
% 1.45/0.59    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_1),
% 1.45/0.59    inference(avatar_component_clause,[],[f67])).
% 1.45/0.59  fof(f67,plain,(
% 1.45/0.59    spl5_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.45/0.59  fof(f60,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.45/0.59    inference(definition_unfolding,[],[f39,f41])).
% 1.45/0.59  fof(f41,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f5])).
% 1.45/0.59  fof(f5,axiom,(
% 1.45/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.59  fof(f39,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f7])).
% 1.45/0.59  fof(f7,axiom,(
% 1.45/0.59    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.45/0.59  fof(f443,plain,(
% 1.45/0.59    ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f415,f46])).
% 1.45/0.59  fof(f46,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f20])).
% 1.45/0.59  fof(f20,plain,(
% 1.45/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f2])).
% 1.45/0.59  fof(f2,axiom,(
% 1.45/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.45/0.59  fof(f415,plain,(
% 1.45/0.59    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl5_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f73,f62])).
% 1.45/0.59  fof(f62,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.45/0.59    inference(definition_unfolding,[],[f47,f56])).
% 1.45/0.59  fof(f56,plain,(
% 1.45/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.45/0.59    inference(definition_unfolding,[],[f37,f55])).
% 1.45/0.59  fof(f55,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.45/0.59    inference(definition_unfolding,[],[f40,f48])).
% 1.45/0.59  fof(f48,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f10])).
% 1.45/0.59  fof(f10,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.59  fof(f40,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f9])).
% 1.45/0.59  fof(f9,axiom,(
% 1.45/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.59  fof(f37,plain,(
% 1.45/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f8])).
% 1.45/0.59  fof(f8,axiom,(
% 1.45/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.59  fof(f47,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f21])).
% 1.45/0.59  fof(f21,plain,(
% 1.45/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f11])).
% 1.45/0.59  fof(f11,axiom,(
% 1.45/0.59    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.45/0.59  fof(f73,plain,(
% 1.45/0.59    r2_hidden(sK1,sK0) | ~spl5_2),
% 1.45/0.59    inference(avatar_component_clause,[],[f71])).
% 1.45/0.59  fof(f71,plain,(
% 1.45/0.59    spl5_2 <=> r2_hidden(sK1,sK0)),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.45/0.59  fof(f412,plain,(
% 1.45/0.59    ~spl5_4 | spl5_1 | spl5_2),
% 1.45/0.59    inference(avatar_split_clause,[],[f168,f71,f67,f106])).
% 1.45/0.59  fof(f106,plain,(
% 1.45/0.59    spl5_4 <=> r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.45/0.59  fof(f168,plain,(
% 1.45/0.59    ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl5_1 | spl5_2)),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f78,f98,f44])).
% 1.45/0.59  fof(f44,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f28])).
% 1.45/0.59  fof(f28,plain,(
% 1.45/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).
% 1.45/0.59  fof(f27,plain,(
% 1.45/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f18,plain,(
% 1.45/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(ennf_transformation,[],[f15])).
% 1.45/0.59  fof(f15,plain,(
% 1.45/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(rectify,[],[f3])).
% 1.45/0.59  fof(f3,axiom,(
% 1.45/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.59  fof(f98,plain,(
% 1.45/0.59    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0) | spl5_1),
% 1.45/0.59    inference(subsumption_resolution,[],[f97,f65])).
% 1.45/0.59  fof(f65,plain,(
% 1.45/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.45/0.59    inference(equality_resolution,[],[f49])).
% 1.45/0.59  fof(f49,plain,(
% 1.45/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f33,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.45/0.59  fof(f32,plain,(
% 1.45/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f31,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(rectify,[],[f30])).
% 1.45/0.59  fof(f30,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(flattening,[],[f29])).
% 1.45/0.59  fof(f29,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(nnf_transformation,[],[f1])).
% 1.45/0.59  fof(f1,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.45/0.59  fof(f97,plain,(
% 1.45/0.59    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl5_1),
% 1.45/0.59    inference(trivial_inequality_removal,[],[f96])).
% 1.45/0.59  fof(f96,plain,(
% 1.45/0.59    sK0 != sK0 | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl5_1),
% 1.45/0.59    inference(superposition,[],[f85,f59])).
% 1.45/0.59  fof(f59,plain,(
% 1.45/0.59    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.45/0.59    inference(definition_unfolding,[],[f36,f41])).
% 1.45/0.59  fof(f36,plain,(
% 1.45/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.59    inference(cnf_transformation,[],[f6])).
% 1.45/0.59  fof(f6,axiom,(
% 1.45/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.45/0.59  fof(f85,plain,(
% 1.45/0.59    ( ! [X0] : (sK0 != k5_xboole_0(sK0,X0) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),sK0) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),X0)) ) | spl5_1),
% 1.45/0.59    inference(superposition,[],[f69,f52])).
% 1.45/0.59  fof(f52,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f69,plain,(
% 1.45/0.59    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_1),
% 1.45/0.59    inference(avatar_component_clause,[],[f67])).
% 1.45/0.59  fof(f78,plain,(
% 1.45/0.59    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl5_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f72,f61])).
% 1.45/0.59  fof(f61,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.45/0.59    inference(definition_unfolding,[],[f45,f56])).
% 1.45/0.59  fof(f45,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f19,plain,(
% 1.45/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f12])).
% 1.45/0.59  fof(f12,axiom,(
% 1.45/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.45/0.59  fof(f72,plain,(
% 1.45/0.59    ~r2_hidden(sK1,sK0) | spl5_2),
% 1.45/0.59    inference(avatar_component_clause,[],[f71])).
% 1.45/0.59  fof(f407,plain,(
% 1.45/0.59    ~spl5_3),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f406])).
% 1.45/0.59  fof(f406,plain,(
% 1.45/0.59    $false | ~spl5_3),
% 1.45/0.59    inference(subsumption_resolution,[],[f382,f399])).
% 1.45/0.59  fof(f399,plain,(
% 1.45/0.59    ( ! [X0] : (~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),X0)) ) | ~spl5_3),
% 1.45/0.59    inference(forward_demodulation,[],[f391,f59])).
% 1.45/0.59  fof(f391,plain,(
% 1.45/0.59    ( ! [X0] : (~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) ) | ~spl5_3),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f60,f175,f44])).
% 1.45/0.59  fof(f175,plain,(
% 1.45/0.59    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k1_xboole_0) | ~spl5_3),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f104,f64])).
% 1.45/0.59  fof(f64,plain,(
% 1.45/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.45/0.59    inference(equality_resolution,[],[f50])).
% 1.45/0.59  fof(f50,plain,(
% 1.45/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f104,plain,(
% 1.45/0.59    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | ~spl5_3),
% 1.45/0.59    inference(avatar_component_clause,[],[f102])).
% 1.45/0.59  fof(f102,plain,(
% 1.45/0.59    spl5_3 <=> r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.45/0.59  fof(f382,plain,(
% 1.45/0.59    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0))) | ~spl5_3),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f104,f175,f63])).
% 1.45/0.59  fof(f63,plain,(
% 1.45/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.45/0.59    inference(equality_resolution,[],[f51])).
% 1.45/0.59  fof(f51,plain,(
% 1.45/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f109,plain,(
% 1.45/0.59    spl5_3 | spl5_4 | spl5_1),
% 1.45/0.59    inference(avatar_split_clause,[],[f100,f67,f106,f102])).
% 1.45/0.59  fof(f100,plain,(
% 1.45/0.59    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl5_1),
% 1.45/0.59    inference(trivial_inequality_removal,[],[f99])).
% 1.45/0.59  fof(f99,plain,(
% 1.45/0.59    sK0 != sK0 | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl5_1),
% 1.45/0.59    inference(superposition,[],[f86,f59])).
% 1.45/0.59  fof(f86,plain,(
% 1.45/0.59    ( ! [X1] : (sK0 != k5_xboole_0(sK0,X1) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1)) ) | spl5_1),
% 1.45/0.59    inference(superposition,[],[f69,f53])).
% 1.45/0.59  fof(f53,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f75,plain,(
% 1.45/0.59    spl5_1 | ~spl5_2),
% 1.45/0.59    inference(avatar_split_clause,[],[f58,f71,f67])).
% 1.45/0.59  fof(f58,plain,(
% 1.45/0.59    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.45/0.59    inference(definition_unfolding,[],[f34,f41,f56])).
% 1.45/0.59  fof(f34,plain,(
% 1.45/0.59    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.45/0.59    inference(cnf_transformation,[],[f24])).
% 1.45/0.59  fof(f24,plain,(
% 1.45/0.59    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.45/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.45/0.59  fof(f23,plain,(
% 1.45/0.59    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f22,plain,(
% 1.45/0.59    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.45/0.59    inference(nnf_transformation,[],[f16])).
% 1.45/0.59  fof(f16,plain,(
% 1.45/0.59    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.45/0.59    inference(ennf_transformation,[],[f14])).
% 1.45/0.59  fof(f14,negated_conjecture,(
% 1.45/0.59    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.45/0.59    inference(negated_conjecture,[],[f13])).
% 1.45/0.59  fof(f13,conjecture,(
% 1.45/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.45/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.45/0.59  fof(f74,plain,(
% 1.45/0.59    ~spl5_1 | spl5_2),
% 1.45/0.59    inference(avatar_split_clause,[],[f57,f71,f67])).
% 1.45/0.59  fof(f57,plain,(
% 1.45/0.59    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.45/0.59    inference(definition_unfolding,[],[f35,f41,f56])).
% 1.45/0.59  fof(f35,plain,(
% 1.45/0.59    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.45/0.59    inference(cnf_transformation,[],[f24])).
% 1.45/0.59  % SZS output end Proof for theBenchmark
% 1.45/0.59  % (27341)------------------------------
% 1.45/0.59  % (27341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (27341)Termination reason: Refutation
% 1.45/0.59  
% 1.45/0.59  % (27341)Memory used [KB]: 11001
% 1.45/0.59  % (27341)Time elapsed: 0.152 s
% 1.45/0.59  % (27341)------------------------------
% 1.45/0.59  % (27341)------------------------------
% 1.45/0.60  % (27314)Success in time 0.223 s
%------------------------------------------------------------------------------
