%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:37 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 116 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  233 ( 298 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f157,f160,f179,f189])).

fof(f189,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f183,f34])).

fof(f34,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK2))
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK2))
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f183,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f152,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f152,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f179,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl5_4 ),
    inference(resolution,[],[f161,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f88,plain,(
    ! [X1] : sP0(k1_xboole_0,X1,X1) ),
    inference(superposition,[],[f68,f86])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f41])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f161,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f34,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f160,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f156,f34])).

fof(f156,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_6
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f157,plain,
    ( spl5_5
    | ~ spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f148,f140,f154,f150])).

fof(f140,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f148,plain,
    ( ~ r2_hidden(sK1,sK2)
    | v1_xboole_0(sK2)
    | spl5_3 ),
    inference(resolution,[],[f142,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f142,plain,
    ( ~ m1_subset_1(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f147,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f137,f144,f140])).

fof(f137,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK1,sK2) ),
    inference(resolution,[],[f63,f62])).

fof(f62,plain,(
    ~ m1_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK2)) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (427)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (437)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (421)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (411)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (423)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (411)Refutation not found, incomplete strategy% (411)------------------------------
% 0.20/0.54  % (411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (411)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (411)Memory used [KB]: 10746
% 0.20/0.54  % (411)Time elapsed: 0.120 s
% 0.20/0.54  % (411)------------------------------
% 0.20/0.54  % (411)------------------------------
% 0.20/0.54  % (419)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (409)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (409)Refutation not found, incomplete strategy% (409)------------------------------
% 0.20/0.54  % (409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (409)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (409)Memory used [KB]: 1663
% 0.20/0.54  % (409)Time elapsed: 0.124 s
% 0.20/0.54  % (409)------------------------------
% 0.20/0.54  % (409)------------------------------
% 1.34/0.54  % (415)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.54  % (421)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f190,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f147,f157,f160,f179,f189])).
% 1.34/0.54  fof(f189,plain,(
% 1.34/0.54    ~spl5_5),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f188])).
% 1.34/0.54  fof(f188,plain,(
% 1.34/0.54    $false | ~spl5_5),
% 1.34/0.54    inference(resolution,[],[f183,f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    r2_hidden(sK1,sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK2)) & r2_hidden(sK1,sK2)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK2)) & r2_hidden(sK1,sK2))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.34/0.54    inference(negated_conjecture,[],[f12])).
% 1.34/0.54  fof(f12,conjecture,(
% 1.34/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.34/0.54  fof(f183,plain,(
% 1.34/0.54    ( ! [X3] : (~r2_hidden(X3,sK2)) ) | ~spl5_5),
% 1.34/0.54    inference(resolution,[],[f152,f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(rectify,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(nnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.54  fof(f152,plain,(
% 1.34/0.54    v1_xboole_0(sK2) | ~spl5_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f150])).
% 1.34/0.54  fof(f150,plain,(
% 1.34/0.54    spl5_5 <=> v1_xboole_0(sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.34/0.54  fof(f179,plain,(
% 1.34/0.54    ~spl5_4),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f177])).
% 1.34/0.54  fof(f177,plain,(
% 1.34/0.54    $false | ~spl5_4),
% 1.34/0.54    inference(resolution,[],[f161,f91])).
% 1.34/0.54  fof(f91,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.34/0.54    inference(condensation,[],[f90])).
% 1.34/0.54  fof(f90,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.34/0.54    inference(resolution,[],[f88,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.34/0.54    inference(rectify,[],[f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.34/0.54    inference(flattening,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.34/0.54    inference(nnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.54  fof(f88,plain,(
% 1.34/0.54    ( ! [X1] : (sP0(k1_xboole_0,X1,X1)) )),
% 1.34/0.54    inference(superposition,[],[f68,f86])).
% 1.34/0.54  fof(f86,plain,(
% 1.34/0.54    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.34/0.54    inference(resolution,[],[f65,f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.34/0.54    inference(definition_unfolding,[],[f47,f41])).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.34/0.54    inference(nnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.34/0.54    inference(equality_resolution,[],[f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.34/0.54    inference(definition_unfolding,[],[f56,f41])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.54    inference(nnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.34/0.54    inference(definition_folding,[],[f2,f18])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.34/0.54  fof(f161,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_xboole_0) | ~spl5_4),
% 1.34/0.54    inference(backward_demodulation,[],[f34,f146])).
% 1.34/0.54  fof(f146,plain,(
% 1.34/0.54    k1_xboole_0 = sK2 | ~spl5_4),
% 1.34/0.54    inference(avatar_component_clause,[],[f144])).
% 1.34/0.54  fof(f144,plain,(
% 1.34/0.54    spl5_4 <=> k1_xboole_0 = sK2),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.34/0.54  fof(f160,plain,(
% 1.34/0.54    spl5_6),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f158])).
% 1.34/0.54  fof(f158,plain,(
% 1.34/0.54    $false | spl5_6),
% 1.34/0.54    inference(resolution,[],[f156,f34])).
% 1.34/0.54  fof(f156,plain,(
% 1.34/0.54    ~r2_hidden(sK1,sK2) | spl5_6),
% 1.34/0.54    inference(avatar_component_clause,[],[f154])).
% 1.34/0.54  fof(f154,plain,(
% 1.34/0.54    spl5_6 <=> r2_hidden(sK1,sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.34/0.54  fof(f157,plain,(
% 1.34/0.54    spl5_5 | ~spl5_6 | spl5_3),
% 1.34/0.54    inference(avatar_split_clause,[],[f148,f140,f154,f150])).
% 1.34/0.54  fof(f140,plain,(
% 1.34/0.54    spl5_3 <=> m1_subset_1(sK1,sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.34/0.54  fof(f148,plain,(
% 1.34/0.54    ~r2_hidden(sK1,sK2) | v1_xboole_0(sK2) | spl5_3),
% 1.34/0.54    inference(resolution,[],[f142,f43])).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.34/0.54    inference(nnf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.34/0.54  fof(f142,plain,(
% 1.34/0.54    ~m1_subset_1(sK1,sK2) | spl5_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f140])).
% 1.34/0.54  fof(f147,plain,(
% 1.34/0.54    ~spl5_3 | spl5_4),
% 1.34/0.54    inference(avatar_split_clause,[],[f137,f144,f140])).
% 1.34/0.54  fof(f137,plain,(
% 1.34/0.54    k1_xboole_0 = sK2 | ~m1_subset_1(sK1,sK2)),
% 1.34/0.54    inference(resolution,[],[f63,f62])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ~m1_subset_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK2))),
% 1.34/0.54    inference(definition_unfolding,[],[f35,f61])).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f37,f60])).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f40,f59])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f49,f58])).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK2))),
% 1.34/0.54    inference(cnf_transformation,[],[f21])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X0,X1] : (m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f46,f61])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 1.34/0.54    inference(flattening,[],[f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (421)------------------------------
% 1.34/0.54  % (421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (421)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (421)Memory used [KB]: 6268
% 1.34/0.54  % (421)Time elapsed: 0.105 s
% 1.34/0.54  % (421)------------------------------
% 1.34/0.54  % (421)------------------------------
% 1.34/0.55  % (408)Success in time 0.184 s
%------------------------------------------------------------------------------
