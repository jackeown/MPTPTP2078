%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:29 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 166 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  256 ( 505 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f1001,f1010,f1020,f1086])).

fof(f1086,plain,
    ( ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f1085])).

fof(f1085,plain,
    ( $false
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f1026,f80])).

fof(f80,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_2
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1026,plain,
    ( r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK0,sK1))
    | spl6_4 ),
    inference(forward_demodulation,[],[f1023,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (9846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f1023,plain,
    ( r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK1,sK0))
    | spl6_4 ),
    inference(resolution,[],[f1009,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1009,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl6_4
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1020,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1013,f37])).

fof(f37,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25])).

fof(f25,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1013,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_3 ),
    inference(resolution,[],[f1005,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1005,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1003,plain,
    ( spl6_3
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1010,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f908,f1007,f1003])).

fof(f908,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f51,f68])).

fof(f68,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1001,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f999,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(sK2,sK1) ) ),
    inference(superposition,[],[f43,f84])).

fof(f84,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f999,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | spl6_1 ),
    inference(forward_demodulation,[],[f998,f118])).

fof(f118,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(X2,sK1)) ),
    inference(resolution,[],[f113,f47])).

fof(f113,plain,(
    ! [X0] : r1_xboole_0(sK2,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f107,f40])).

fof(f107,plain,(
    ! [X0] : r1_xboole_0(sK2,k3_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f998,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | spl6_1 ),
    inference(forward_demodulation,[],[f995,f40])).

fof(f995,plain,
    ( r2_hidden(sK3,k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | spl6_1 ),
    inference(resolution,[],[f988,f506])).

fof(f506,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f77,f46])).

fof(f77,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_1
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f61])).

% (9851)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f988,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | r2_hidden(sK3,k3_xboole_0(X0,sK2)) ) ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f81,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f73,f79,f75])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ) ),
    inference(superposition,[],[f43,f72])).

fof(f72,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f35,f62])).

fof(f35,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.53  % (9855)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (9832)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.54  % (9834)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (9847)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.55  % (9829)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.55  % (9850)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.55  % (9839)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.56  % (9842)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.56  % (9837)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.56  % (9848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.57  % (9840)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.57  % (9845)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.58  % (9853)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.68/0.58  % (9848)Refutation not found, incomplete strategy% (9848)------------------------------
% 1.68/0.58  % (9848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (9848)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (9848)Memory used [KB]: 10746
% 1.68/0.58  % (9830)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.68/0.58  % (9848)Time elapsed: 0.156 s
% 1.68/0.58  % (9848)------------------------------
% 1.68/0.58  % (9848)------------------------------
% 1.86/0.60  % (9836)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.86/0.60  % (9828)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.86/0.60  % (9835)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.86/0.61  % (9827)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.86/0.61  % (9852)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.86/0.61  % (9831)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.86/0.62  % (9844)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.86/0.62  % (9843)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.86/0.62  % (9849)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.86/0.62  % (9829)Refutation found. Thanks to Tanya!
% 1.86/0.62  % SZS status Theorem for theBenchmark
% 1.86/0.62  % SZS output start Proof for theBenchmark
% 1.86/0.62  fof(f1087,plain,(
% 1.86/0.62    $false),
% 1.86/0.62    inference(avatar_sat_refutation,[],[f81,f1001,f1010,f1020,f1086])).
% 1.86/0.62  fof(f1086,plain,(
% 1.86/0.62    ~spl6_2 | spl6_4),
% 1.86/0.62    inference(avatar_contradiction_clause,[],[f1085])).
% 1.86/0.62  fof(f1085,plain,(
% 1.86/0.62    $false | (~spl6_2 | spl6_4)),
% 1.86/0.62    inference(subsumption_resolution,[],[f1026,f80])).
% 1.86/0.62  fof(f80,plain,(
% 1.86/0.62    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | ~spl6_2),
% 1.86/0.62    inference(avatar_component_clause,[],[f79])).
% 1.86/0.62  fof(f79,plain,(
% 1.86/0.62    spl6_2 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK1))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.86/0.62  fof(f1026,plain,(
% 1.86/0.62    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK0,sK1)) | spl6_4),
% 1.86/0.62    inference(forward_demodulation,[],[f1023,f40])).
% 1.86/0.62  fof(f40,plain,(
% 1.86/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f1])).
% 1.86/0.62  fof(f1,axiom,(
% 1.86/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.86/0.62  % (9846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.86/0.62  fof(f1023,plain,(
% 1.86/0.62    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK1,sK0)) | spl6_4),
% 1.86/0.62    inference(resolution,[],[f1009,f42])).
% 1.86/0.62  fof(f42,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f28])).
% 1.86/0.62  fof(f28,plain,(
% 1.86/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.86/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).
% 1.86/0.62  fof(f27,plain,(
% 1.86/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.86/0.62    introduced(choice_axiom,[])).
% 1.86/0.62  fof(f19,plain,(
% 1.86/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.86/0.62    inference(ennf_transformation,[],[f16])).
% 1.86/0.62  fof(f16,plain,(
% 1.86/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.86/0.62    inference(rectify,[],[f5])).
% 1.86/0.62  fof(f5,axiom,(
% 1.86/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.86/0.62  fof(f1009,plain,(
% 1.86/0.62    ~r1_xboole_0(sK1,sK0) | spl6_4),
% 1.86/0.62    inference(avatar_component_clause,[],[f1007])).
% 1.86/0.62  fof(f1007,plain,(
% 1.86/0.62    spl6_4 <=> r1_xboole_0(sK1,sK0)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.86/0.62  fof(f1020,plain,(
% 1.86/0.62    spl6_3),
% 1.86/0.62    inference(avatar_contradiction_clause,[],[f1019])).
% 1.86/0.62  fof(f1019,plain,(
% 1.86/0.62    $false | spl6_3),
% 1.86/0.62    inference(subsumption_resolution,[],[f1013,f37])).
% 1.86/0.62  fof(f37,plain,(
% 1.86/0.62    r1_xboole_0(sK2,sK1)),
% 1.86/0.62    inference(cnf_transformation,[],[f26])).
% 1.86/0.62  fof(f26,plain,(
% 1.86/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.86/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25])).
% 1.86/0.62  fof(f25,plain,(
% 1.86/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.86/0.62    introduced(choice_axiom,[])).
% 1.86/0.62  fof(f18,plain,(
% 1.86/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.86/0.62    inference(flattening,[],[f17])).
% 1.86/0.62  fof(f17,plain,(
% 1.86/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.86/0.62    inference(ennf_transformation,[],[f15])).
% 1.86/0.62  fof(f15,negated_conjecture,(
% 1.86/0.62    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.86/0.62    inference(negated_conjecture,[],[f14])).
% 1.86/0.62  fof(f14,conjecture,(
% 1.86/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.86/0.62  fof(f1013,plain,(
% 1.86/0.62    ~r1_xboole_0(sK2,sK1) | spl6_3),
% 1.86/0.62    inference(resolution,[],[f1005,f46])).
% 1.86/0.62  fof(f46,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f22])).
% 1.86/0.62  fof(f22,plain,(
% 1.86/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.86/0.62    inference(ennf_transformation,[],[f4])).
% 1.86/0.62  fof(f4,axiom,(
% 1.86/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.86/0.62  fof(f1005,plain,(
% 1.86/0.62    ~r1_xboole_0(sK1,sK2) | spl6_3),
% 1.86/0.62    inference(avatar_component_clause,[],[f1003])).
% 1.86/0.62  fof(f1003,plain,(
% 1.86/0.62    spl6_3 <=> r1_xboole_0(sK1,sK2)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.86/0.62  fof(f1010,plain,(
% 1.86/0.62    ~spl6_3 | ~spl6_4),
% 1.86/0.62    inference(avatar_split_clause,[],[f908,f1007,f1003])).
% 1.86/0.62  fof(f908,plain,(
% 1.86/0.62    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.86/0.62    inference(resolution,[],[f51,f68])).
% 1.86/0.62  fof(f68,plain,(
% 1.86/0.62    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.86/0.62    inference(resolution,[],[f46,f38])).
% 1.86/0.62  fof(f38,plain,(
% 1.86/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.86/0.62    inference(cnf_transformation,[],[f26])).
% 1.86/0.62  fof(f51,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f23])).
% 1.86/0.62  fof(f23,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.86/0.62    inference(ennf_transformation,[],[f8])).
% 1.86/0.62  fof(f8,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.86/0.62  fof(f1001,plain,(
% 1.86/0.62    spl6_1),
% 1.86/0.62    inference(avatar_contradiction_clause,[],[f1000])).
% 1.86/0.62  fof(f1000,plain,(
% 1.86/0.62    $false | spl6_1),
% 1.86/0.62    inference(subsumption_resolution,[],[f999,f91])).
% 1.86/0.62  fof(f91,plain,(
% 1.86/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.86/0.62    inference(subsumption_resolution,[],[f88,f37])).
% 1.86/0.62  fof(f88,plain,(
% 1.86/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(sK2,sK1)) )),
% 1.86/0.62    inference(superposition,[],[f43,f84])).
% 1.86/0.62  fof(f84,plain,(
% 1.86/0.62    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.86/0.62    inference(resolution,[],[f47,f37])).
% 1.86/0.62  fof(f47,plain,(
% 1.86/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.86/0.62    inference(cnf_transformation,[],[f29])).
% 1.86/0.62  fof(f29,plain,(
% 1.86/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.86/0.62    inference(nnf_transformation,[],[f3])).
% 1.86/0.62  fof(f3,axiom,(
% 1.86/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.86/0.62  fof(f43,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f28])).
% 1.86/0.62  fof(f999,plain,(
% 1.86/0.62    r2_hidden(sK3,k1_xboole_0) | spl6_1),
% 1.86/0.62    inference(forward_demodulation,[],[f998,f118])).
% 1.86/0.62  fof(f118,plain,(
% 1.86/0.62    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(X2,sK1))) )),
% 1.86/0.62    inference(resolution,[],[f113,f47])).
% 1.86/0.62  fof(f113,plain,(
% 1.86/0.62    ( ! [X0] : (r1_xboole_0(sK2,k3_xboole_0(X0,sK1))) )),
% 1.86/0.62    inference(superposition,[],[f107,f40])).
% 1.86/0.62  fof(f107,plain,(
% 1.86/0.62    ( ! [X0] : (r1_xboole_0(sK2,k3_xboole_0(sK1,X0))) )),
% 1.86/0.62    inference(resolution,[],[f60,f37])).
% 1.86/0.62  fof(f60,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f24])).
% 1.86/0.62  fof(f24,plain,(
% 1.86/0.62    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.86/0.62    inference(ennf_transformation,[],[f9])).
% 1.86/0.62  fof(f9,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.86/0.62  fof(f998,plain,(
% 1.86/0.62    r2_hidden(sK3,k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | spl6_1),
% 1.86/0.62    inference(forward_demodulation,[],[f995,f40])).
% 1.86/0.62  fof(f995,plain,(
% 1.86/0.62    r2_hidden(sK3,k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | spl6_1),
% 1.86/0.62    inference(resolution,[],[f988,f506])).
% 1.86/0.62  fof(f506,plain,(
% 1.86/0.62    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl6_1),
% 1.86/0.62    inference(resolution,[],[f64,f82])).
% 1.86/0.62  fof(f82,plain,(
% 1.86/0.62    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl6_1),
% 1.86/0.62    inference(resolution,[],[f77,f46])).
% 1.86/0.62  fof(f77,plain,(
% 1.86/0.62    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_1),
% 1.86/0.62    inference(avatar_component_clause,[],[f75])).
% 1.86/0.62  fof(f75,plain,(
% 1.86/0.62    spl6_1 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.86/0.62  fof(f64,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.86/0.62    inference(definition_unfolding,[],[f44,f62])).
% 1.86/0.62  fof(f62,plain,(
% 1.86/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.86/0.62    inference(definition_unfolding,[],[f39,f61])).
% 1.86/0.62  % (9851)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.86/0.62  fof(f61,plain,(
% 1.86/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.86/0.62    inference(definition_unfolding,[],[f41,f49])).
% 1.86/0.62  fof(f49,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f12])).
% 1.86/0.62  fof(f12,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.86/0.62  fof(f41,plain,(
% 1.86/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f11])).
% 1.86/0.62  fof(f11,axiom,(
% 1.86/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.86/0.62  fof(f39,plain,(
% 1.86/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f10])).
% 1.86/0.62  fof(f10,axiom,(
% 1.86/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.86/0.62  fof(f44,plain,(
% 1.86/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f20])).
% 1.86/0.62  fof(f20,plain,(
% 1.86/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.86/0.62    inference(ennf_transformation,[],[f13])).
% 1.86/0.62  fof(f13,axiom,(
% 1.86/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.86/0.62  fof(f988,plain,(
% 1.86/0.62    ( ! [X0] : (~r2_hidden(sK3,X0) | r2_hidden(sK3,k3_xboole_0(X0,sK2))) )),
% 1.86/0.62    inference(resolution,[],[f65,f36])).
% 1.86/0.62  fof(f36,plain,(
% 1.86/0.62    r2_hidden(sK3,sK2)),
% 1.86/0.62    inference(cnf_transformation,[],[f26])).
% 1.86/0.62  fof(f65,plain,(
% 1.86/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.86/0.62    inference(equality_resolution,[],[f56])).
% 1.86/0.62  fof(f56,plain,(
% 1.86/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.86/0.62    inference(cnf_transformation,[],[f34])).
% 1.86/0.62  fof(f34,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.86/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.86/0.62  fof(f33,plain,(
% 1.86/0.62    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.86/0.62    introduced(choice_axiom,[])).
% 1.86/0.62  fof(f32,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.86/0.62    inference(rectify,[],[f31])).
% 1.86/0.62  fof(f31,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.86/0.62    inference(flattening,[],[f30])).
% 1.86/0.62  fof(f30,plain,(
% 1.86/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.86/0.62    inference(nnf_transformation,[],[f2])).
% 1.86/0.62  fof(f2,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.86/0.62  fof(f81,plain,(
% 1.86/0.62    ~spl6_1 | spl6_2),
% 1.86/0.62    inference(avatar_split_clause,[],[f73,f79,f75])).
% 1.86/0.62  fof(f73,plain,(
% 1.86/0.62    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))) )),
% 1.86/0.62    inference(superposition,[],[f43,f72])).
% 1.86/0.62  fof(f72,plain,(
% 1.86/0.62    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.86/0.62    inference(resolution,[],[f45,f63])).
% 1.86/0.62  fof(f63,plain,(
% 1.86/0.62    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.86/0.62    inference(definition_unfolding,[],[f35,f62])).
% 1.86/0.62  fof(f35,plain,(
% 1.86/0.62    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.86/0.62    inference(cnf_transformation,[],[f26])).
% 1.86/0.62  fof(f45,plain,(
% 1.86/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.86/0.62    inference(cnf_transformation,[],[f21])).
% 1.86/0.62  fof(f21,plain,(
% 1.86/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.86/0.62    inference(ennf_transformation,[],[f7])).
% 1.86/0.62  fof(f7,axiom,(
% 1.86/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.86/0.62  % SZS output end Proof for theBenchmark
% 1.86/0.62  % (9829)------------------------------
% 1.86/0.62  % (9829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.62  % (9829)Termination reason: Refutation
% 1.86/0.62  
% 1.86/0.62  % (9829)Memory used [KB]: 11257
% 1.86/0.62  % (9829)Time elapsed: 0.193 s
% 1.86/0.62  % (9829)------------------------------
% 1.86/0.62  % (9829)------------------------------
% 1.86/0.62  % (9841)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.03/0.63  % (9820)Success in time 0.269 s
%------------------------------------------------------------------------------
