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
% DateTime   : Thu Dec  3 12:41:06 EST 2020

% Result     : Theorem 5.58s
% Output     : Refutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 152 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  326 ( 411 expanded)
%              Number of equality atoms :  149 ( 203 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f618,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f99,f561,f567,f582,f595,f617])).

fof(f617,plain,
    ( spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f613,f95])).

fof(f95,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f613,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f601,f112])).

fof(f112,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f109,f64])).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f109,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f84,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

% (7828)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% (7632)Time limit reached!
% (7632)------------------------------
% (7632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7632)Termination reason: Time limit
% (7632)Termination phase: Saturation

% (7632)Memory used [KB]: 12409
% (7632)Time elapsed: 0.600 s
% (7632)------------------------------
% (7632)------------------------------
fof(f601,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_tarski(sK0))
        | r2_hidden(X2,sK1) )
    | ~ spl4_7 ),
    inference(superposition,[],[f88,f593])).

fof(f593,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl4_7
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f595,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f589,f579,f591])).

fof(f579,plain,
    ( spl4_6
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f589,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f586,f289])).

fof(f289,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f269,f269])).

fof(f269,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f256,f75])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f256,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f235,f101])).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f75,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f235,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f74,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f586,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),sK1)
    | ~ spl4_6 ),
    inference(superposition,[],[f71,f581])).

fof(f581,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f579])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f582,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f575,f90,f579])).

fof(f90,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f575,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f569,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f569,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f62,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f567,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f563,f96])).

fof(f96,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f563,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_5 ),
    inference(resolution,[],[f560,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f560,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl4_5
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f561,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f551,f90,f558])).

fof(f551,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f91,f535])).

fof(f535,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f525,f68])).

fof(f525,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f63,f518])).

fof(f518,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X7,X8) = X7
      | ~ r1_tarski(X7,X8) ) ),
    inference(forward_demodulation,[],[f517,f256])).

fof(f517,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X8,X7))
      | ~ r1_tarski(X7,X8) ) ),
    inference(forward_demodulation,[],[f488,f75])).

fof(f488,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X7,X8) = k5_xboole_0(k5_xboole_0(X8,X7),X8)
      | ~ r1_tarski(X7,X8) ) ),
    inference(superposition,[],[f200,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f200,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f71,f75])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f91,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f98,f94,f90])).

fof(f98,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f45,f96])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f97,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f94,f90])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7625)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (7648)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (7640)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (7634)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (7636)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (7633)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (7635)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (7632)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (7629)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (7641)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (7630)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (7631)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (7646)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (7647)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (7627)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (7626)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (7638)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (7628)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7637)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (7653)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (7649)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.54  % (7644)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.54  % (7654)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.55  % (7639)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.55  % (7651)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.55  % (7650)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.55  % (7645)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (7652)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.55/0.56  % (7643)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.57  % (7642)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 3.15/0.82  % (7630)Time limit reached!
% 3.15/0.82  % (7630)------------------------------
% 3.15/0.82  % (7630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.82  % (7630)Termination reason: Time limit
% 3.15/0.82  % (7630)Termination phase: Saturation
% 3.15/0.82  
% 3.15/0.82  % (7630)Memory used [KB]: 10234
% 3.15/0.82  % (7630)Time elapsed: 0.400 s
% 3.15/0.82  % (7630)------------------------------
% 3.15/0.82  % (7630)------------------------------
% 3.86/0.90  % (7633)Refutation not found, incomplete strategy% (7633)------------------------------
% 3.86/0.90  % (7633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.90  % (7633)Termination reason: Refutation not found, incomplete strategy
% 3.86/0.90  
% 3.86/0.90  % (7633)Memory used [KB]: 14328
% 3.86/0.90  % (7633)Time elapsed: 0.492 s
% 3.86/0.90  % (7633)------------------------------
% 3.86/0.90  % (7633)------------------------------
% 3.86/0.90  % (7637)Time limit reached!
% 3.86/0.90  % (7637)------------------------------
% 3.86/0.90  % (7637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.90  % (7637)Termination reason: Time limit
% 3.86/0.90  
% 3.86/0.90  % (7637)Memory used [KB]: 10874
% 3.86/0.90  % (7637)Time elapsed: 0.503 s
% 3.86/0.90  % (7637)------------------------------
% 3.86/0.90  % (7637)------------------------------
% 3.86/0.91  % (7635)Time limit reached!
% 3.86/0.91  % (7635)------------------------------
% 3.86/0.91  % (7635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.91  % (7625)Time limit reached!
% 3.86/0.91  % (7625)------------------------------
% 3.86/0.91  % (7625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.91  % (7625)Termination reason: Time limit
% 3.86/0.91  % (7625)Termination phase: Saturation
% 3.86/0.91  
% 3.86/0.91  % (7625)Memory used [KB]: 3837
% 3.86/0.91  % (7625)Time elapsed: 0.500 s
% 3.86/0.91  % (7625)------------------------------
% 3.86/0.91  % (7625)------------------------------
% 3.86/0.92  % (7626)Time limit reached!
% 3.86/0.92  % (7626)------------------------------
% 3.86/0.92  % (7626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.92  % (7626)Termination reason: Time limit
% 3.86/0.92  % (7626)Termination phase: Saturation
% 3.86/0.92  
% 3.86/0.92  % (7626)Memory used [KB]: 8827
% 3.86/0.92  % (7626)Time elapsed: 0.500 s
% 3.86/0.92  % (7626)------------------------------
% 3.86/0.92  % (7626)------------------------------
% 4.40/0.93  % (7635)Termination reason: Time limit
% 4.40/0.93  % (7635)Termination phase: Saturation
% 4.40/0.93  
% 4.40/0.93  % (7635)Memory used [KB]: 16375
% 4.40/0.93  % (7635)Time elapsed: 0.500 s
% 4.40/0.93  % (7635)------------------------------
% 4.40/0.93  % (7635)------------------------------
% 4.40/0.93  % (7642)Time limit reached!
% 4.40/0.93  % (7642)------------------------------
% 4.40/0.93  % (7642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.93  % (7642)Termination reason: Time limit
% 4.40/0.93  
% 4.40/0.93  % (7642)Memory used [KB]: 14711
% 4.40/0.93  % (7642)Time elapsed: 0.522 s
% 4.40/0.93  % (7642)------------------------------
% 4.40/0.93  % (7642)------------------------------
% 4.40/0.95  % (7773)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.63/1.00  % (7653)Time limit reached!
% 4.63/1.00  % (7653)------------------------------
% 4.63/1.00  % (7653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.00  % (7653)Termination reason: Time limit
% 4.63/1.00  % (7653)Termination phase: Saturation
% 4.63/1.00  
% 4.63/1.00  % (7653)Memory used [KB]: 9338
% 4.63/1.00  % (7653)Time elapsed: 0.600 s
% 4.63/1.00  % (7653)------------------------------
% 4.63/1.00  % (7653)------------------------------
% 4.63/1.02  % (7819)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.63/1.03  % (7814)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.07/1.04  % (7815)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.07/1.04  % (7641)Time limit reached!
% 5.07/1.04  % (7641)------------------------------
% 5.07/1.04  % (7641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.04  % (7641)Termination reason: Time limit
% 5.07/1.04  
% 5.07/1.04  % (7641)Memory used [KB]: 17014
% 5.07/1.04  % (7641)Time elapsed: 0.634 s
% 5.07/1.04  % (7641)------------------------------
% 5.07/1.04  % (7641)------------------------------
% 5.07/1.05  % (7824)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.07/1.06  % (7829)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.58/1.08  % (7824)Refutation found. Thanks to Tanya!
% 5.58/1.08  % SZS status Theorem for theBenchmark
% 5.58/1.08  % SZS output start Proof for theBenchmark
% 5.58/1.08  fof(f618,plain,(
% 5.58/1.08    $false),
% 5.58/1.08    inference(avatar_sat_refutation,[],[f97,f99,f561,f567,f582,f595,f617])).
% 5.58/1.08  fof(f617,plain,(
% 5.58/1.08    spl4_2 | ~spl4_7),
% 5.58/1.08    inference(avatar_contradiction_clause,[],[f616])).
% 5.58/1.08  fof(f616,plain,(
% 5.58/1.08    $false | (spl4_2 | ~spl4_7)),
% 5.58/1.08    inference(subsumption_resolution,[],[f613,f95])).
% 5.58/1.08  fof(f95,plain,(
% 5.58/1.08    ~r2_hidden(sK0,sK1) | spl4_2),
% 5.58/1.08    inference(avatar_component_clause,[],[f94])).
% 5.58/1.08  fof(f94,plain,(
% 5.58/1.08    spl4_2 <=> r2_hidden(sK0,sK1)),
% 5.58/1.08    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 5.58/1.08  fof(f613,plain,(
% 5.58/1.08    r2_hidden(sK0,sK1) | ~spl4_7),
% 5.58/1.08    inference(resolution,[],[f601,f112])).
% 5.58/1.08  fof(f112,plain,(
% 5.58/1.08    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 5.58/1.08    inference(superposition,[],[f109,f64])).
% 5.58/1.08  fof(f64,plain,(
% 5.58/1.08    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 5.58/1.08    inference(cnf_transformation,[],[f14])).
% 5.58/1.08  fof(f14,axiom,(
% 5.58/1.08    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 5.58/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 5.58/1.08  fof(f109,plain,(
% 5.58/1.08    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 5.58/1.08    inference(superposition,[],[f84,f70])).
% 5.58/1.08  fof(f70,plain,(
% 5.58/1.08    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 5.58/1.08    inference(cnf_transformation,[],[f15])).
% 5.58/1.08  fof(f15,axiom,(
% 5.58/1.08    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 5.58/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 5.58/1.08  fof(f84,plain,(
% 5.58/1.08    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 5.58/1.08    inference(equality_resolution,[],[f83])).
% 5.58/1.08  fof(f83,plain,(
% 5.58/1.08    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 5.58/1.08    inference(equality_resolution,[],[f47])).
% 5.58/1.08  fof(f47,plain,(
% 5.58/1.08    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 5.58/1.08    inference(cnf_transformation,[],[f37])).
% 5.58/1.08  fof(f37,plain,(
% 5.58/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.58/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 5.58/1.08  fof(f36,plain,(
% 5.58/1.08    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 5.58/1.08    introduced(choice_axiom,[])).
% 5.58/1.08  fof(f35,plain,(
% 5.58/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.58/1.08    inference(rectify,[],[f34])).
% 5.58/1.08  fof(f34,plain,(
% 5.58/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.58/1.08    inference(flattening,[],[f33])).
% 5.58/1.08  fof(f33,plain,(
% 5.58/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.58/1.08    inference(nnf_transformation,[],[f28])).
% 5.58/1.08  fof(f28,plain,(
% 5.58/1.08    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 5.58/1.08    inference(ennf_transformation,[],[f13])).
% 5.58/1.08  fof(f13,axiom,(
% 5.58/1.08    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 5.58/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 5.58/1.08  % (7828)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.58/1.08  % (7632)Time limit reached!
% 5.58/1.08  % (7632)------------------------------
% 5.58/1.08  % (7632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.58/1.08  % (7632)Termination reason: Time limit
% 5.58/1.08  % (7632)Termination phase: Saturation
% 5.58/1.08  
% 5.58/1.08  % (7632)Memory used [KB]: 12409
% 5.58/1.08  % (7632)Time elapsed: 0.600 s
% 5.58/1.08  % (7632)------------------------------
% 5.58/1.08  % (7632)------------------------------
% 5.58/1.09  fof(f601,plain,(
% 5.58/1.09    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK0)) | r2_hidden(X2,sK1)) ) | ~spl4_7),
% 5.58/1.09    inference(superposition,[],[f88,f593])).
% 5.58/1.09  fof(f593,plain,(
% 5.58/1.09    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_7),
% 5.58/1.09    inference(avatar_component_clause,[],[f591])).
% 5.58/1.09  fof(f591,plain,(
% 5.58/1.09    spl4_7 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 5.58/1.09    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 5.58/1.09  fof(f88,plain,(
% 5.58/1.09    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 5.58/1.09    inference(equality_resolution,[],[f54])).
% 5.58/1.09  fof(f54,plain,(
% 5.58/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.58/1.09    inference(cnf_transformation,[],[f42])).
% 5.58/1.09  fof(f42,plain,(
% 5.58/1.09    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.58/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 5.58/1.09  fof(f41,plain,(
% 5.58/1.09    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 5.58/1.09    introduced(choice_axiom,[])).
% 5.58/1.09  fof(f40,plain,(
% 5.58/1.09    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.58/1.09    inference(rectify,[],[f39])).
% 5.58/1.09  fof(f39,plain,(
% 5.58/1.09    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.58/1.09    inference(flattening,[],[f38])).
% 5.58/1.09  fof(f38,plain,(
% 5.58/1.09    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.58/1.09    inference(nnf_transformation,[],[f2])).
% 5.58/1.09  fof(f2,axiom,(
% 5.58/1.09    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 5.58/1.09  fof(f595,plain,(
% 5.58/1.09    spl4_7 | ~spl4_6),
% 5.58/1.09    inference(avatar_split_clause,[],[f589,f579,f591])).
% 5.58/1.09  fof(f579,plain,(
% 5.58/1.09    spl4_6 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 5.58/1.09    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 5.58/1.09  fof(f589,plain,(
% 5.58/1.09    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_6),
% 5.58/1.09    inference(forward_demodulation,[],[f586,f289])).
% 5.58/1.09  fof(f289,plain,(
% 5.58/1.09    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 5.58/1.09    inference(superposition,[],[f269,f269])).
% 5.58/1.09  fof(f269,plain,(
% 5.58/1.09    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 5.58/1.09    inference(superposition,[],[f256,f75])).
% 5.58/1.09  fof(f75,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.58/1.09    inference(cnf_transformation,[],[f1])).
% 5.58/1.09  fof(f1,axiom,(
% 5.58/1.09    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.58/1.09  fof(f256,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.58/1.09    inference(forward_demodulation,[],[f235,f101])).
% 5.58/1.09  fof(f101,plain,(
% 5.58/1.09    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.58/1.09    inference(superposition,[],[f75,f66])).
% 5.58/1.09  fof(f66,plain,(
% 5.58/1.09    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.58/1.09    inference(cnf_transformation,[],[f8])).
% 5.58/1.09  fof(f8,axiom,(
% 5.58/1.09    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 5.58/1.09  fof(f235,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.58/1.09    inference(superposition,[],[f74,f68])).
% 5.58/1.09  fof(f68,plain,(
% 5.58/1.09    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.58/1.09    inference(cnf_transformation,[],[f10])).
% 5.58/1.09  fof(f10,axiom,(
% 5.58/1.09    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.58/1.09  fof(f74,plain,(
% 5.58/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.58/1.09    inference(cnf_transformation,[],[f9])).
% 5.58/1.09  fof(f9,axiom,(
% 5.58/1.09    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.58/1.09  fof(f586,plain,(
% 5.58/1.09    k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),sK1) | ~spl4_6),
% 5.58/1.09    inference(superposition,[],[f71,f581])).
% 5.58/1.09  fof(f581,plain,(
% 5.58/1.09    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_6),
% 5.58/1.09    inference(avatar_component_clause,[],[f579])).
% 5.58/1.09  fof(f71,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 5.58/1.09    inference(cnf_transformation,[],[f11])).
% 5.58/1.09  fof(f11,axiom,(
% 5.58/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 5.58/1.09  fof(f582,plain,(
% 5.58/1.09    spl4_6 | ~spl4_1),
% 5.58/1.09    inference(avatar_split_clause,[],[f575,f90,f579])).
% 5.58/1.09  fof(f90,plain,(
% 5.58/1.09    spl4_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.58/1.09    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 5.58/1.09  fof(f575,plain,(
% 5.58/1.09    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_1),
% 5.58/1.09    inference(forward_demodulation,[],[f569,f67])).
% 5.58/1.09  fof(f67,plain,(
% 5.58/1.09    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.58/1.09    inference(cnf_transformation,[],[f6])).
% 5.58/1.09  fof(f6,axiom,(
% 5.58/1.09    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 5.58/1.09  fof(f569,plain,(
% 5.58/1.09    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl4_1),
% 5.58/1.09    inference(superposition,[],[f62,f92])).
% 5.58/1.09  fof(f92,plain,(
% 5.58/1.09    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 5.58/1.09    inference(avatar_component_clause,[],[f90])).
% 5.58/1.09  fof(f62,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.58/1.09    inference(cnf_transformation,[],[f7])).
% 5.58/1.09  fof(f7,axiom,(
% 5.58/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.58/1.09  fof(f567,plain,(
% 5.58/1.09    ~spl4_2 | spl4_5),
% 5.58/1.09    inference(avatar_contradiction_clause,[],[f566])).
% 5.58/1.09  fof(f566,plain,(
% 5.58/1.09    $false | (~spl4_2 | spl4_5)),
% 5.58/1.09    inference(subsumption_resolution,[],[f563,f96])).
% 5.58/1.09  fof(f96,plain,(
% 5.58/1.09    r2_hidden(sK0,sK1) | ~spl4_2),
% 5.58/1.09    inference(avatar_component_clause,[],[f94])).
% 5.58/1.09  fof(f563,plain,(
% 5.58/1.09    ~r2_hidden(sK0,sK1) | spl4_5),
% 5.58/1.09    inference(resolution,[],[f560,f61])).
% 5.58/1.09  fof(f61,plain,(
% 5.58/1.09    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 5.58/1.09    inference(cnf_transformation,[],[f43])).
% 5.58/1.09  fof(f43,plain,(
% 5.58/1.09    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 5.58/1.09    inference(nnf_transformation,[],[f21])).
% 5.58/1.09  fof(f21,axiom,(
% 5.58/1.09    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 5.58/1.09  fof(f560,plain,(
% 5.58/1.09    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_5),
% 5.58/1.09    inference(avatar_component_clause,[],[f558])).
% 5.58/1.09  fof(f558,plain,(
% 5.58/1.09    spl4_5 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 5.58/1.09    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 5.58/1.09  fof(f561,plain,(
% 5.58/1.09    ~spl4_5 | spl4_1),
% 5.58/1.09    inference(avatar_split_clause,[],[f551,f90,f558])).
% 5.58/1.09  fof(f551,plain,(
% 5.58/1.09    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 5.58/1.09    inference(trivial_inequality_removal,[],[f542])).
% 5.58/1.09  fof(f542,plain,(
% 5.58/1.09    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 5.58/1.09    inference(superposition,[],[f91,f535])).
% 5.58/1.09  fof(f535,plain,(
% 5.58/1.09    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 5.58/1.09    inference(forward_demodulation,[],[f525,f68])).
% 5.58/1.09  fof(f525,plain,(
% 5.58/1.09    ( ! [X2,X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 5.58/1.09    inference(superposition,[],[f63,f518])).
% 5.58/1.09  fof(f518,plain,(
% 5.58/1.09    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = X7 | ~r1_tarski(X7,X8)) )),
% 5.58/1.09    inference(forward_demodulation,[],[f517,f256])).
% 5.58/1.09  fof(f517,plain,(
% 5.58/1.09    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X8,X7)) | ~r1_tarski(X7,X8)) )),
% 5.58/1.09    inference(forward_demodulation,[],[f488,f75])).
% 5.58/1.09  fof(f488,plain,(
% 5.58/1.09    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(k5_xboole_0(X8,X7),X8) | ~r1_tarski(X7,X8)) )),
% 5.58/1.09    inference(superposition,[],[f200,f73])).
% 5.58/1.09  fof(f73,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 5.58/1.09    inference(cnf_transformation,[],[f29])).
% 5.58/1.09  fof(f29,plain,(
% 5.58/1.09    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.58/1.09    inference(ennf_transformation,[],[f5])).
% 5.58/1.09  fof(f5,axiom,(
% 5.58/1.09    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.58/1.09  fof(f200,plain,(
% 5.58/1.09    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 5.58/1.09    inference(superposition,[],[f71,f75])).
% 5.58/1.09  fof(f63,plain,(
% 5.58/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.58/1.09    inference(cnf_transformation,[],[f4])).
% 5.58/1.09  fof(f4,axiom,(
% 5.58/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.58/1.09  fof(f91,plain,(
% 5.58/1.09    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 5.58/1.09    inference(avatar_component_clause,[],[f90])).
% 5.58/1.09  fof(f99,plain,(
% 5.58/1.09    ~spl4_1 | ~spl4_2),
% 5.58/1.09    inference(avatar_split_clause,[],[f98,f94,f90])).
% 5.58/1.09  fof(f98,plain,(
% 5.58/1.09    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_2),
% 5.58/1.09    inference(subsumption_resolution,[],[f45,f96])).
% 5.58/1.09  fof(f45,plain,(
% 5.58/1.09    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.58/1.09    inference(cnf_transformation,[],[f32])).
% 5.58/1.09  fof(f32,plain,(
% 5.58/1.09    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 5.58/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 5.58/1.09  fof(f31,plain,(
% 5.58/1.09    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 5.58/1.09    introduced(choice_axiom,[])).
% 5.58/1.09  fof(f30,plain,(
% 5.58/1.09    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 5.58/1.09    inference(nnf_transformation,[],[f27])).
% 5.58/1.09  fof(f27,plain,(
% 5.58/1.09    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 5.58/1.09    inference(ennf_transformation,[],[f25])).
% 5.58/1.09  fof(f25,negated_conjecture,(
% 5.58/1.09    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.58/1.09    inference(negated_conjecture,[],[f24])).
% 5.58/1.09  fof(f24,conjecture,(
% 5.58/1.09    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.58/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 5.58/1.09  fof(f97,plain,(
% 5.58/1.09    spl4_1 | spl4_2),
% 5.58/1.09    inference(avatar_split_clause,[],[f44,f94,f90])).
% 5.58/1.09  fof(f44,plain,(
% 5.58/1.09    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.58/1.09    inference(cnf_transformation,[],[f32])).
% 5.58/1.09  % SZS output end Proof for theBenchmark
% 5.58/1.09  % (7824)------------------------------
% 5.58/1.09  % (7824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.58/1.09  % (7824)Termination reason: Refutation
% 5.58/1.09  
% 5.58/1.09  % (7824)Memory used [KB]: 11129
% 5.58/1.09  % (7824)Time elapsed: 0.115 s
% 5.58/1.09  % (7824)------------------------------
% 5.58/1.09  % (7824)------------------------------
% 5.58/1.10  % (7624)Success in time 0.733 s
%------------------------------------------------------------------------------
