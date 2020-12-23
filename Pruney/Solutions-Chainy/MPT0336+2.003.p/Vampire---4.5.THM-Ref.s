%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:23 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 141 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  246 ( 437 expanded)
%              Number of equality atoms :   95 ( 117 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f851,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f169,f832,f850])).

fof(f850,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f849])).

fof(f849,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f847,f838])).

fof(f838,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f256,f82])).

fof(f82,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f80,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f80,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f42,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f256,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f112,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f112,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f90,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f43,f46])).

fof(f43,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f847,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f155,f46])).

fof(f155,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f832,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f831])).

fof(f831,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f829,f68])).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f829,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f822,f46])).

fof(f822,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f821])).

fof(f821,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(superposition,[],[f697,f66])).

fof(f697,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(superposition,[],[f202,f352])).

fof(f352,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f341,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f341,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f151,f82])).

fof(f151,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_tarski(sK3),X0)
    | ~ spl6_2 ),
    inference(superposition,[],[f63,f109])).

fof(f109,plain,
    ( k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_2
  <=> k3_xboole_0(sK0,sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f63,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f202,plain,(
    k1_xboole_0 != k3_xboole_0(k1_tarski(sK3),sK2) ),
    inference(resolution,[],[f192,f67])).

fof(f192,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK2) ),
    inference(resolution,[],[f141,f46])).

fof(f141,plain,(
    ~ r1_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(superposition,[],[f122,f62])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f122,plain,(
    ! [X0] : ~ r1_xboole_0(sK2,k2_tarski(X0,sK3)) ),
    inference(resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f41,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f169,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f164,f154,f103])).

fof(f103,plain,
    ( spl6_1
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f164,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(resolution,[],[f156,f67])).

fof(f156,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f110,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f99,f107,f103])).

fof(f99,plain,
    ( k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f40,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:53:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (5801)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.49  % (5809)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (5826)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (5827)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (5805)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.26/0.53  % (5808)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.53  % (5828)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.26/0.53  % (5803)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.53  % (5830)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.53  % (5806)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.54  % (5824)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.54  % (5802)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.54  % (5812)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.26/0.54  % (5815)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.54  % (5804)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.43/0.54  % (5819)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.54  % (5829)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.54  % (5831)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.55  % (5831)Refutation not found, incomplete strategy% (5831)------------------------------
% 1.43/0.55  % (5831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (5831)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (5831)Memory used [KB]: 1663
% 1.43/0.55  % (5831)Time elapsed: 0.136 s
% 1.43/0.55  % (5831)------------------------------
% 1.43/0.55  % (5831)------------------------------
% 1.43/0.55  % (5807)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (5822)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.55  % (5817)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (5817)Refutation not found, incomplete strategy% (5817)------------------------------
% 1.43/0.55  % (5817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (5817)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (5817)Memory used [KB]: 10618
% 1.43/0.55  % (5817)Time elapsed: 0.147 s
% 1.43/0.55  % (5817)------------------------------
% 1.43/0.55  % (5817)------------------------------
% 1.43/0.55  % (5811)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.55  % (5825)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.55  % (5823)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.55  % (5813)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.56  % (5816)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.56  % (5814)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.56  % (5810)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.57  % (5820)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.57  % (5818)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.07/0.63  % (5813)Refutation found. Thanks to Tanya!
% 2.07/0.63  % SZS status Theorem for theBenchmark
% 2.07/0.63  % SZS output start Proof for theBenchmark
% 2.07/0.63  fof(f851,plain,(
% 2.07/0.63    $false),
% 2.07/0.63    inference(avatar_sat_refutation,[],[f110,f169,f832,f850])).
% 2.07/0.63  fof(f850,plain,(
% 2.07/0.63    ~spl6_3),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f849])).
% 2.07/0.63  fof(f849,plain,(
% 2.07/0.63    $false | ~spl6_3),
% 2.07/0.63    inference(subsumption_resolution,[],[f847,f838])).
% 2.07/0.63  fof(f838,plain,(
% 2.07/0.63    ~r1_xboole_0(sK1,sK0)),
% 2.07/0.63    inference(subsumption_resolution,[],[f256,f82])).
% 2.07/0.63  fof(f82,plain,(
% 2.07/0.63    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 2.07/0.63    inference(resolution,[],[f80,f66])).
% 2.07/0.63  fof(f66,plain,(
% 2.07/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f39])).
% 2.07/0.63  fof(f39,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.07/0.63    inference(nnf_transformation,[],[f3])).
% 2.07/0.63  fof(f3,axiom,(
% 2.07/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.07/0.63  fof(f80,plain,(
% 2.07/0.63    r1_xboole_0(sK1,sK2)),
% 2.07/0.63    inference(resolution,[],[f42,f46])).
% 2.07/0.63  fof(f46,plain,(
% 2.07/0.63    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f25])).
% 2.07/0.63  fof(f25,plain,(
% 2.07/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f4])).
% 2.07/0.63  fof(f4,axiom,(
% 2.07/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.07/0.63  fof(f42,plain,(
% 2.07/0.63    r1_xboole_0(sK2,sK1)),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  fof(f29,plain,(
% 2.07/0.63    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.07/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).
% 2.07/0.63  fof(f28,plain,(
% 2.07/0.63    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 2.07/0.63    introduced(choice_axiom,[])).
% 2.07/0.63  fof(f23,plain,(
% 2.07/0.63    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.07/0.63    inference(flattening,[],[f22])).
% 2.07/0.63  fof(f22,plain,(
% 2.07/0.63    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.07/0.63    inference(ennf_transformation,[],[f20])).
% 2.07/0.63  fof(f20,negated_conjecture,(
% 2.07/0.63    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.07/0.63    inference(negated_conjecture,[],[f19])).
% 2.07/0.63  fof(f19,conjecture,(
% 2.07/0.63    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.07/0.63  fof(f256,plain,(
% 2.07/0.63    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 2.07/0.63    inference(superposition,[],[f112,f44])).
% 2.07/0.63  fof(f44,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f24])).
% 2.07/0.63  fof(f24,plain,(
% 2.07/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f12])).
% 2.07/0.63  fof(f12,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 2.07/0.63  fof(f112,plain,(
% 2.07/0.63    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 2.07/0.63    inference(resolution,[],[f90,f67])).
% 2.07/0.63  fof(f67,plain,(
% 2.07/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.07/0.63    inference(cnf_transformation,[],[f39])).
% 2.07/0.63  fof(f90,plain,(
% 2.07/0.63    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 2.07/0.63    inference(resolution,[],[f43,f46])).
% 2.07/0.63  fof(f43,plain,(
% 2.07/0.63    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  fof(f847,plain,(
% 2.07/0.63    r1_xboole_0(sK1,sK0) | ~spl6_3),
% 2.07/0.63    inference(resolution,[],[f155,f46])).
% 2.07/0.63  fof(f155,plain,(
% 2.07/0.63    r1_xboole_0(sK0,sK1) | ~spl6_3),
% 2.07/0.63    inference(avatar_component_clause,[],[f154])).
% 2.07/0.63  fof(f154,plain,(
% 2.07/0.63    spl6_3 <=> r1_xboole_0(sK0,sK1)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.07/0.63  fof(f832,plain,(
% 2.07/0.63    ~spl6_2),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f831])).
% 2.07/0.63  fof(f831,plain,(
% 2.07/0.63    $false | ~spl6_2),
% 2.07/0.63    inference(subsumption_resolution,[],[f829,f68])).
% 2.07/0.63  fof(f68,plain,(
% 2.07/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f11])).
% 2.07/0.63  fof(f11,axiom,(
% 2.07/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.07/0.63  fof(f829,plain,(
% 2.07/0.63    ~r1_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 2.07/0.63    inference(resolution,[],[f822,f46])).
% 2.07/0.63  fof(f822,plain,(
% 2.07/0.63    ~r1_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 2.07/0.63    inference(trivial_inequality_removal,[],[f821])).
% 2.07/0.63  fof(f821,plain,(
% 2.07/0.63    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 2.07/0.63    inference(superposition,[],[f697,f66])).
% 2.07/0.63  fof(f697,plain,(
% 2.07/0.63    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 2.07/0.63    inference(superposition,[],[f202,f352])).
% 2.07/0.63  fof(f352,plain,(
% 2.07/0.63    k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 2.07/0.63    inference(forward_demodulation,[],[f341,f64])).
% 2.07/0.63  fof(f64,plain,(
% 2.07/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f2])).
% 2.07/0.63  fof(f2,axiom,(
% 2.07/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.07/0.63  fof(f341,plain,(
% 2.07/0.63    k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 2.07/0.63    inference(superposition,[],[f151,f82])).
% 2.07/0.63  fof(f151,plain,(
% 2.07/0.63    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_tarski(sK3),X0)) ) | ~spl6_2),
% 2.07/0.63    inference(superposition,[],[f63,f109])).
% 2.07/0.63  fof(f109,plain,(
% 2.07/0.63    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | ~spl6_2),
% 2.07/0.63    inference(avatar_component_clause,[],[f107])).
% 2.07/0.63  fof(f107,plain,(
% 2.07/0.63    spl6_2 <=> k3_xboole_0(sK0,sK1) = k1_tarski(sK3)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.07/0.63  fof(f63,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.07/0.63    inference(cnf_transformation,[],[f8])).
% 2.07/0.63  fof(f8,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.07/0.63  fof(f202,plain,(
% 2.07/0.63    k1_xboole_0 != k3_xboole_0(k1_tarski(sK3),sK2)),
% 2.07/0.63    inference(resolution,[],[f192,f67])).
% 2.07/0.63  fof(f192,plain,(
% 2.07/0.63    ~r1_xboole_0(k1_tarski(sK3),sK2)),
% 2.07/0.63    inference(resolution,[],[f141,f46])).
% 2.07/0.63  fof(f141,plain,(
% 2.07/0.63    ~r1_xboole_0(sK2,k1_tarski(sK3))),
% 2.07/0.63    inference(superposition,[],[f122,f62])).
% 2.07/0.63  fof(f62,plain,(
% 2.07/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f15])).
% 2.07/0.63  fof(f15,axiom,(
% 2.07/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.07/0.63  fof(f122,plain,(
% 2.07/0.63    ( ! [X0] : (~r1_xboole_0(sK2,k2_tarski(X0,sK3))) )),
% 2.07/0.63    inference(resolution,[],[f76,f70])).
% 2.07/0.63  fof(f70,plain,(
% 2.07/0.63    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.07/0.63    inference(equality_resolution,[],[f69])).
% 2.07/0.63  fof(f69,plain,(
% 2.07/0.63    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.07/0.63    inference(equality_resolution,[],[f49])).
% 2.07/0.63  fof(f49,plain,(
% 2.07/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f34])).
% 2.07/0.63  fof(f34,plain,(
% 2.07/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.07/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 2.07/0.63  fof(f33,plain,(
% 2.07/0.63    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.07/0.63    introduced(choice_axiom,[])).
% 2.07/0.63  fof(f32,plain,(
% 2.07/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.07/0.63    inference(rectify,[],[f31])).
% 2.07/0.63  fof(f31,plain,(
% 2.07/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.07/0.63    inference(flattening,[],[f30])).
% 2.07/0.63  fof(f30,plain,(
% 2.07/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.07/0.63    inference(nnf_transformation,[],[f14])).
% 2.07/0.63  fof(f14,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.07/0.63  fof(f76,plain,(
% 2.07/0.63    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) )),
% 2.07/0.63    inference(resolution,[],[f41,f55])).
% 2.07/0.63  fof(f55,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f36])).
% 2.07/0.63  fof(f36,plain,(
% 2.07/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.07/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f35])).
% 2.07/0.63  fof(f35,plain,(
% 2.07/0.63    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.07/0.63    introduced(choice_axiom,[])).
% 2.07/0.63  fof(f26,plain,(
% 2.07/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.07/0.63    inference(ennf_transformation,[],[f21])).
% 2.07/0.63  fof(f21,plain,(
% 2.07/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.07/0.63    inference(rectify,[],[f5])).
% 2.07/0.63  fof(f5,axiom,(
% 2.07/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.07/0.63  fof(f41,plain,(
% 2.07/0.63    r2_hidden(sK3,sK2)),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  fof(f169,plain,(
% 2.07/0.63    ~spl6_1 | spl6_3),
% 2.07/0.63    inference(avatar_split_clause,[],[f164,f154,f103])).
% 2.07/0.63  fof(f103,plain,(
% 2.07/0.63    spl6_1 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.07/0.63  fof(f164,plain,(
% 2.07/0.63    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl6_3),
% 2.07/0.63    inference(resolution,[],[f156,f67])).
% 2.07/0.63  fof(f156,plain,(
% 2.07/0.63    ~r1_xboole_0(sK0,sK1) | spl6_3),
% 2.07/0.63    inference(avatar_component_clause,[],[f154])).
% 2.07/0.63  fof(f110,plain,(
% 2.07/0.63    spl6_1 | spl6_2),
% 2.07/0.63    inference(avatar_split_clause,[],[f99,f107,f103])).
% 2.07/0.63  fof(f99,plain,(
% 2.07/0.63    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 2.07/0.63    inference(resolution,[],[f40,f59])).
% 2.07/0.63  fof(f59,plain,(
% 2.07/0.63    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.07/0.63    inference(cnf_transformation,[],[f38])).
% 2.07/0.63  fof(f38,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.07/0.63    inference(flattening,[],[f37])).
% 2.07/0.63  fof(f37,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.07/0.63    inference(nnf_transformation,[],[f18])).
% 2.07/0.63  fof(f18,axiom,(
% 2.07/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.07/0.63  fof(f40,plain,(
% 2.07/0.63    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  % SZS output end Proof for theBenchmark
% 2.07/0.63  % (5813)------------------------------
% 2.07/0.63  % (5813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (5813)Termination reason: Refutation
% 2.07/0.63  
% 2.07/0.63  % (5813)Memory used [KB]: 11129
% 2.07/0.63  % (5813)Time elapsed: 0.224 s
% 2.07/0.63  % (5813)------------------------------
% 2.07/0.63  % (5813)------------------------------
% 2.07/0.65  % (5798)Success in time 0.292 s
%------------------------------------------------------------------------------
