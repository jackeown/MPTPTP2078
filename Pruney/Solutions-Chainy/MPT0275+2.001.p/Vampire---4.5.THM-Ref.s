%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:25 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 284 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  331 (1075 expanded)
%              Number of equality atoms :   90 ( 262 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f90,f480,f560,f707])).

fof(f707,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f705,f83])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f705,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f697])).

fof(f697,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f55,f679])).

fof(f679,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f667,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f667,plain,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) = k4_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f498,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f498,plain,
    ( ! [X2] : k4_xboole_0(X2,sK2) = k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f490,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f490,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,sK2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f59,f78])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f560,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f555,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f555,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f499,f478])).

fof(f478,plain,
    ( ! [X26,X25] : r2_hidden(X25,k2_xboole_0(X26,k1_tarski(X25)))
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f477])).

fof(f477,plain,
    ( ! [X26,X25] :
        ( k1_xboole_0 != k1_xboole_0
        | r2_hidden(X25,k2_xboole_0(X26,k1_tarski(X25))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f55,f229])).

fof(f229,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f218,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f218,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))
    | ~ spl5_2 ),
    inference(superposition,[],[f195,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f195,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f189,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f189,plain,
    ( ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X3,X3)
    | ~ spl5_2 ),
    inference(superposition,[],[f49,f175])).

fof(f175,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_2 ),
    inference(resolution,[],[f171,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f171,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_2 ),
    inference(resolution,[],[f164,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f164,plain,
    ( ! [X5] : ~ r2_hidden(X5,k1_xboole_0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f160,f103])).

fof(f103,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f74,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f160,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | r2_hidden(X5,sK2) )
    | ~ spl5_2 ),
    inference(superposition,[],[f75,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f45,f106])).

fof(f106,plain,
    ( sK2 = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f98,f43])).

fof(f98,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK0)) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f50,f92])).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f499,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
        | r2_hidden(X3,sK2) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f491,f164])).

fof(f491,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
        | r2_hidden(X3,sK2)
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f73,f78])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f480,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f467,f79])).

fof(f79,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f467,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f229,f132])).

fof(f132,plain,
    ( sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f127,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f46,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f127,plain,
    ( sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f93,f86])).

fof(f86,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(X0),k1_tarski(sK0))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f91,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f91,plain,
    ( ! [X0] :
        ( sK2 = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(sK0)),sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f82,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f48])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f90,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f70,f81,f77])).

fof(f70,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f39,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f89,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f69,f85,f77])).

fof(f69,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f40,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f68,f85,f81,f77])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:21:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (11827)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.14/0.51  % (11848)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.14/0.52  % (11840)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.14/0.52  % (11832)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.14/0.52  % (11830)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.14/0.52  % (11825)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.14/0.52  % (11840)Refutation not found, incomplete strategy% (11840)------------------------------
% 1.14/0.52  % (11840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (11840)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.52  
% 1.14/0.52  % (11840)Memory used [KB]: 6140
% 1.14/0.52  % (11840)Time elapsed: 0.003 s
% 1.14/0.52  % (11840)------------------------------
% 1.14/0.52  % (11840)------------------------------
% 1.14/0.52  % (11835)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.14/0.52  % (11826)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.14/0.52  % (11847)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.14/0.53  % (11838)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.14/0.53  % (11831)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.14/0.53  % (11833)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.14/0.53  % (11851)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.14/0.53  % (11842)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.14/0.53  % (11846)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.53  % (11839)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.54  % (11829)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (11849)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (11852)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (11843)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.55  % (11854)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (11853)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (11847)Refutation not found, incomplete strategy% (11847)------------------------------
% 1.34/0.55  % (11847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (11847)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (11847)Memory used [KB]: 10874
% 1.34/0.55  % (11847)Time elapsed: 0.099 s
% 1.34/0.55  % (11847)------------------------------
% 1.34/0.55  % (11847)------------------------------
% 1.34/0.55  % (11841)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (11837)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (11828)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.55  % (11850)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.55  % (11834)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.55  % (11836)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (11845)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.55  % (11842)Refutation not found, incomplete strategy% (11842)------------------------------
% 1.34/0.55  % (11842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (11842)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (11842)Memory used [KB]: 10618
% 1.34/0.55  % (11842)Time elapsed: 0.147 s
% 1.34/0.55  % (11842)------------------------------
% 1.34/0.55  % (11842)------------------------------
% 1.34/0.55  % (11844)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.58  % (11833)Refutation found. Thanks to Tanya!
% 1.34/0.58  % SZS status Theorem for theBenchmark
% 1.34/0.59  % SZS output start Proof for theBenchmark
% 1.34/0.59  fof(f713,plain,(
% 1.34/0.59    $false),
% 1.34/0.59    inference(avatar_sat_refutation,[],[f88,f89,f90,f480,f560,f707])).
% 1.34/0.59  fof(f707,plain,(
% 1.34/0.59    ~spl5_1 | spl5_2),
% 1.34/0.59    inference(avatar_contradiction_clause,[],[f706])).
% 1.34/0.59  fof(f706,plain,(
% 1.34/0.59    $false | (~spl5_1 | spl5_2)),
% 1.34/0.59    inference(subsumption_resolution,[],[f705,f83])).
% 1.34/0.59  fof(f83,plain,(
% 1.34/0.59    ~r2_hidden(sK0,sK2) | spl5_2),
% 1.34/0.59    inference(avatar_component_clause,[],[f81])).
% 1.34/0.59  fof(f81,plain,(
% 1.34/0.59    spl5_2 <=> r2_hidden(sK0,sK2)),
% 1.34/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.34/0.59  fof(f705,plain,(
% 1.34/0.59    r2_hidden(sK0,sK2) | ~spl5_1),
% 1.34/0.59    inference(trivial_inequality_removal,[],[f697])).
% 1.34/0.59  fof(f697,plain,(
% 1.34/0.59    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,sK2) | ~spl5_1),
% 1.34/0.59    inference(superposition,[],[f55,f679])).
% 1.34/0.59  fof(f679,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK2) | ~spl5_1),
% 1.34/0.59    inference(forward_demodulation,[],[f667,f78])).
% 1.34/0.59  fof(f78,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | ~spl5_1),
% 1.34/0.59    inference(avatar_component_clause,[],[f77])).
% 1.34/0.59  fof(f77,plain,(
% 1.34/0.59    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.34/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.34/0.59  fof(f667,plain,(
% 1.34/0.59    k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) = k4_xboole_0(k1_tarski(sK0),sK2) | ~spl5_1),
% 1.34/0.59    inference(superposition,[],[f498,f51])).
% 1.34/0.59  fof(f51,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f13])).
% 1.34/0.59  fof(f13,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 1.34/0.59  fof(f498,plain,(
% 1.34/0.59    ( ! [X2] : (k4_xboole_0(X2,sK2) = k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),sK2)) ) | ~spl5_1),
% 1.34/0.59    inference(forward_demodulation,[],[f490,f43])).
% 1.34/0.59  fof(f43,plain,(
% 1.34/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.59    inference(cnf_transformation,[],[f5])).
% 1.34/0.59  fof(f5,axiom,(
% 1.34/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.34/0.59  fof(f490,plain,(
% 1.34/0.59    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,sK2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),sK2)) ) | ~spl5_1),
% 1.34/0.59    inference(superposition,[],[f59,f78])).
% 1.34/0.59  fof(f59,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f9])).
% 1.34/0.59  fof(f9,axiom,(
% 1.34/0.59    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.34/0.59  fof(f55,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f33])).
% 1.34/0.59  fof(f33,plain,(
% 1.34/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.34/0.59    inference(nnf_transformation,[],[f18])).
% 1.34/0.59  fof(f18,axiom,(
% 1.34/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.34/0.59  fof(f560,plain,(
% 1.34/0.59    ~spl5_1 | ~spl5_2 | spl5_3),
% 1.34/0.59    inference(avatar_contradiction_clause,[],[f559])).
% 1.34/0.59  fof(f559,plain,(
% 1.34/0.59    $false | (~spl5_1 | ~spl5_2 | spl5_3)),
% 1.34/0.59    inference(subsumption_resolution,[],[f555,f87])).
% 1.34/0.59  fof(f87,plain,(
% 1.34/0.59    ~r2_hidden(sK1,sK2) | spl5_3),
% 1.34/0.59    inference(avatar_component_clause,[],[f85])).
% 1.34/0.59  fof(f85,plain,(
% 1.34/0.59    spl5_3 <=> r2_hidden(sK1,sK2)),
% 1.34/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.34/0.59  fof(f555,plain,(
% 1.34/0.59    r2_hidden(sK1,sK2) | (~spl5_1 | ~spl5_2)),
% 1.34/0.59    inference(resolution,[],[f499,f478])).
% 1.34/0.59  fof(f478,plain,(
% 1.34/0.59    ( ! [X26,X25] : (r2_hidden(X25,k2_xboole_0(X26,k1_tarski(X25)))) ) | ~spl5_2),
% 1.34/0.59    inference(trivial_inequality_removal,[],[f477])).
% 1.34/0.59  fof(f477,plain,(
% 1.34/0.59    ( ! [X26,X25] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(X25,k2_xboole_0(X26,k1_tarski(X25)))) ) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f55,f229])).
% 1.34/0.59  fof(f229,plain,(
% 1.34/0.59    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl5_2),
% 1.34/0.59    inference(forward_demodulation,[],[f218,f50])).
% 1.34/0.59  fof(f50,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f6])).
% 1.34/0.59  fof(f6,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.34/0.59  fof(f218,plain,(
% 1.34/0.59    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) ) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f195,f57])).
% 1.34/0.59  fof(f57,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f8])).
% 1.34/0.59  fof(f8,axiom,(
% 1.34/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.34/0.59  fof(f195,plain,(
% 1.34/0.59    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) ) | ~spl5_2),
% 1.34/0.59    inference(forward_demodulation,[],[f189,f42])).
% 1.34/0.59  fof(f42,plain,(
% 1.34/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f11])).
% 1.34/0.59  fof(f11,axiom,(
% 1.34/0.59    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.34/0.59  fof(f189,plain,(
% 1.34/0.59    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X3,X3)) ) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f49,f175])).
% 1.34/0.59  fof(f175,plain,(
% 1.34/0.59    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl5_2),
% 1.34/0.59    inference(resolution,[],[f171,f52])).
% 1.34/0.59  fof(f52,plain,(
% 1.34/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.34/0.59    inference(cnf_transformation,[],[f23])).
% 1.34/0.59  fof(f23,plain,(
% 1.34/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.34/0.59    inference(ennf_transformation,[],[f4])).
% 1.34/0.59  fof(f4,axiom,(
% 1.34/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.34/0.59  fof(f171,plain,(
% 1.34/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl5_2),
% 1.34/0.59    inference(resolution,[],[f164,f53])).
% 1.34/0.59  fof(f53,plain,(
% 1.34/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f32])).
% 1.34/0.59  fof(f32,plain,(
% 1.34/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).
% 1.34/0.59  fof(f31,plain,(
% 1.34/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.59    introduced(choice_axiom,[])).
% 1.34/0.59  fof(f24,plain,(
% 1.34/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.34/0.59    inference(ennf_transformation,[],[f21])).
% 1.34/0.59  fof(f21,plain,(
% 1.34/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.34/0.59    inference(unused_predicate_definition_removal,[],[f2])).
% 1.34/0.59  fof(f2,axiom,(
% 1.34/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.59  fof(f164,plain,(
% 1.34/0.59    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) ) | ~spl5_2),
% 1.34/0.59    inference(subsumption_resolution,[],[f160,f103])).
% 1.34/0.59  fof(f103,plain,(
% 1.34/0.59    ( ! [X4] : (~r2_hidden(X4,sK2) | ~r2_hidden(X4,k1_xboole_0)) ) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f74,f92])).
% 1.34/0.59  fof(f92,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK2) | ~spl5_2),
% 1.34/0.59    inference(resolution,[],[f82,f56])).
% 1.34/0.59  fof(f56,plain,(
% 1.34/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f33])).
% 1.34/0.59  fof(f82,plain,(
% 1.34/0.59    r2_hidden(sK0,sK2) | ~spl5_2),
% 1.34/0.59    inference(avatar_component_clause,[],[f81])).
% 1.34/0.59  fof(f74,plain,(
% 1.34/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.34/0.59    inference(equality_resolution,[],[f62])).
% 1.34/0.59  fof(f62,plain,(
% 1.34/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.59    inference(cnf_transformation,[],[f38])).
% 1.34/0.59  fof(f38,plain,(
% 1.34/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.34/0.59  fof(f37,plain,(
% 1.34/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.34/0.59    introduced(choice_axiom,[])).
% 1.34/0.59  fof(f36,plain,(
% 1.34/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.59    inference(rectify,[],[f35])).
% 1.34/0.59  fof(f35,plain,(
% 1.34/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.59    inference(flattening,[],[f34])).
% 1.34/0.59  fof(f34,plain,(
% 1.34/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.59    inference(nnf_transformation,[],[f3])).
% 1.34/0.59  fof(f3,axiom,(
% 1.34/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.34/0.59  fof(f160,plain,(
% 1.34/0.59    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,sK2)) ) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f75,f138])).
% 1.34/0.59  fof(f138,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(sK2,sK2) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f45,f106])).
% 1.34/0.59  fof(f106,plain,(
% 1.34/0.59    sK2 = k2_xboole_0(sK2,k1_tarski(sK0)) | ~spl5_2),
% 1.34/0.59    inference(forward_demodulation,[],[f98,f43])).
% 1.34/0.59  fof(f98,plain,(
% 1.34/0.59    k2_xboole_0(sK2,k1_tarski(sK0)) = k2_xboole_0(sK2,k1_xboole_0) | ~spl5_2),
% 1.34/0.59    inference(superposition,[],[f50,f92])).
% 1.34/0.59  fof(f45,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f10])).
% 1.34/0.59  fof(f10,axiom,(
% 1.34/0.59    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.34/0.59  fof(f75,plain,(
% 1.34/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.34/0.59    inference(equality_resolution,[],[f61])).
% 1.34/0.59  fof(f61,plain,(
% 1.34/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.59    inference(cnf_transformation,[],[f38])).
% 1.34/0.59  fof(f49,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f7])).
% 1.34/0.59  fof(f7,axiom,(
% 1.34/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.34/0.59  fof(f499,plain,(
% 1.34/0.59    ( ! [X3] : (~r2_hidden(X3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | r2_hidden(X3,sK2)) ) | (~spl5_1 | ~spl5_2)),
% 1.34/0.59    inference(subsumption_resolution,[],[f491,f164])).
% 1.34/0.59  fof(f491,plain,(
% 1.34/0.59    ( ! [X3] : (~r2_hidden(X3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | r2_hidden(X3,sK2) | r2_hidden(X3,k1_xboole_0)) ) | ~spl5_1),
% 1.34/0.59    inference(superposition,[],[f73,f78])).
% 1.34/0.59  fof(f73,plain,(
% 1.34/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.34/0.59    inference(equality_resolution,[],[f63])).
% 1.34/0.59  fof(f63,plain,(
% 1.34/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.59    inference(cnf_transformation,[],[f38])).
% 1.34/0.59  fof(f480,plain,(
% 1.34/0.59    spl5_1 | ~spl5_2 | ~spl5_3),
% 1.34/0.59    inference(avatar_contradiction_clause,[],[f479])).
% 1.34/0.59  fof(f479,plain,(
% 1.34/0.59    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.34/0.59    inference(subsumption_resolution,[],[f467,f79])).
% 1.34/0.59  fof(f79,plain,(
% 1.34/0.59    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | spl5_1),
% 1.34/0.59    inference(avatar_component_clause,[],[f77])).
% 1.34/0.59  fof(f467,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | (~spl5_2 | ~spl5_3)),
% 1.34/0.59    inference(superposition,[],[f229,f132])).
% 1.34/0.59  fof(f132,plain,(
% 1.34/0.59    sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_2 | ~spl5_3)),
% 1.34/0.59    inference(forward_demodulation,[],[f127,f71])).
% 1.34/0.59  fof(f71,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 1.34/0.59    inference(definition_unfolding,[],[f46,f48,f48])).
% 1.34/0.59  fof(f48,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f15])).
% 1.34/0.59  fof(f15,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.34/0.59  fof(f46,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f14])).
% 1.34/0.59  fof(f14,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.34/0.59  fof(f127,plain,(
% 1.34/0.59    sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | (~spl5_2 | ~spl5_3)),
% 1.34/0.59    inference(resolution,[],[f93,f86])).
% 1.34/0.59  fof(f86,plain,(
% 1.34/0.59    r2_hidden(sK1,sK2) | ~spl5_3),
% 1.34/0.59    inference(avatar_component_clause,[],[f85])).
% 1.34/0.59  fof(f93,plain,(
% 1.34/0.59    ( ! [X0] : (~r2_hidden(X0,sK2) | sK2 = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(X0),k1_tarski(sK0)))) ) | ~spl5_2),
% 1.34/0.59    inference(forward_demodulation,[],[f91,f47])).
% 1.34/0.59  fof(f47,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f1])).
% 1.34/0.59  fof(f1,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.34/0.59  fof(f91,plain,(
% 1.34/0.59    ( ! [X0] : (sK2 = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(sK0)),sK2) | ~r2_hidden(X0,sK2)) ) | ~spl5_2),
% 1.34/0.59    inference(resolution,[],[f82,f72])).
% 1.34/0.59  fof(f72,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.34/0.59    inference(definition_unfolding,[],[f60,f48])).
% 1.34/0.59  fof(f60,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f26])).
% 1.34/0.59  fof(f26,plain,(
% 1.34/0.59    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.34/0.59    inference(flattening,[],[f25])).
% 1.34/0.59  fof(f25,plain,(
% 1.34/0.59    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.34/0.59    inference(ennf_transformation,[],[f17])).
% 1.34/0.59  fof(f17,axiom,(
% 1.34/0.59    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.34/0.59  fof(f90,plain,(
% 1.34/0.59    spl5_1 | spl5_2),
% 1.34/0.59    inference(avatar_split_clause,[],[f70,f81,f77])).
% 1.34/0.59  fof(f70,plain,(
% 1.34/0.59    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.34/0.59    inference(definition_unfolding,[],[f39,f48])).
% 1.34/0.59  fof(f39,plain,(
% 1.34/0.59    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.34/0.59    inference(cnf_transformation,[],[f30])).
% 1.34/0.59  fof(f30,plain,(
% 1.34/0.59    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.34/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 1.34/0.59  fof(f29,plain,(
% 1.34/0.59    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.34/0.59    introduced(choice_axiom,[])).
% 1.34/0.59  fof(f28,plain,(
% 1.34/0.59    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.34/0.59    inference(flattening,[],[f27])).
% 1.34/0.59  fof(f27,plain,(
% 1.34/0.59    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.34/0.59    inference(nnf_transformation,[],[f22])).
% 1.34/0.59  fof(f22,plain,(
% 1.34/0.59    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.34/0.59    inference(ennf_transformation,[],[f20])).
% 1.34/0.59  fof(f20,negated_conjecture,(
% 1.34/0.59    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.34/0.59    inference(negated_conjecture,[],[f19])).
% 1.34/0.59  fof(f19,conjecture,(
% 1.34/0.59    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.34/0.59  fof(f89,plain,(
% 1.34/0.59    spl5_1 | spl5_3),
% 1.34/0.59    inference(avatar_split_clause,[],[f69,f85,f77])).
% 1.34/0.59  fof(f69,plain,(
% 1.34/0.59    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.34/0.59    inference(definition_unfolding,[],[f40,f48])).
% 1.34/0.59  fof(f40,plain,(
% 1.34/0.59    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.34/0.59    inference(cnf_transformation,[],[f30])).
% 1.34/0.59  fof(f88,plain,(
% 1.34/0.59    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.34/0.59    inference(avatar_split_clause,[],[f68,f85,f81,f77])).
% 1.34/0.59  fof(f68,plain,(
% 1.34/0.59    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.34/0.59    inference(definition_unfolding,[],[f41,f48])).
% 1.34/0.59  fof(f41,plain,(
% 1.34/0.59    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.34/0.59    inference(cnf_transformation,[],[f30])).
% 1.34/0.59  % SZS output end Proof for theBenchmark
% 1.34/0.59  % (11833)------------------------------
% 1.34/0.59  % (11833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.59  % (11833)Termination reason: Refutation
% 1.34/0.59  
% 1.34/0.59  % (11833)Memory used [KB]: 11001
% 1.34/0.59  % (11833)Time elapsed: 0.154 s
% 1.34/0.59  % (11833)------------------------------
% 1.34/0.59  % (11833)------------------------------
% 1.34/0.59  % (11824)Success in time 0.23 s
%------------------------------------------------------------------------------
