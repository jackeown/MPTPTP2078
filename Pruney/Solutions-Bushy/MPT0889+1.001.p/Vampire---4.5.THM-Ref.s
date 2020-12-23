%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:50 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 284 expanded)
%              Number of leaves         :   26 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  390 ( 868 expanded)
%              Number of equality atoms :  122 ( 323 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f323,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f107,f120,f152,f159,f187,f193,f196,f243,f263,f272,f281,f309])).

fof(f309,plain,
    ( ~ spl4_19
    | spl4_6
    | spl4_4
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f307,f279,f88,f95,f270])).

fof(f270,plain,
    ( spl4_19
  <=> m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f95,plain,
    ( spl4_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f88,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f279,plain,
    ( spl4_21
  <=> sK3(sK0) = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3(sK0)),k6_mcart_1(sK0,sK1,sK2,sK3(sK0)),k7_mcart_1(sK0,sK1,sK2,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f307,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f304])).

fof(f304,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | sK3(sK0) != sK3(sK0)
    | ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl4_21 ),
    inference(resolution,[],[f296,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f54,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK3(sK0)),X0)
        | k1_xboole_0 = X0
        | v1_xboole_0(X0)
        | sK3(X0) != sK3(sK0) )
    | ~ spl4_21 ),
    inference(resolution,[],[f294,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3(sK0)),X0)
        | sK3(X0) != sK3(sK0)
        | k1_xboole_0 = X0 )
    | ~ spl4_21 ),
    inference(superposition,[],[f39,f280])).

fof(f280,plain,
    ( sK3(sK0) = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3(sK0)),k6_mcart_1(sK0,sK1,sK2,sK3(sK0)),k7_mcart_1(sK0,sK1,sK2,sK3(sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f279])).

fof(f39,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f281,plain,
    ( spl4_4
    | spl4_9
    | spl4_8
    | spl4_21
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f277,f270,f279,f128,f131,f88])).

fof(f131,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f128,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f277,plain,
    ( sK3(sK0) = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3(sK0)),k6_mcart_1(sK0,sK1,sK2,sK3(sK0)),k7_mcart_1(sK0,sK1,sK2,sK3(sK0)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_19 ),
    inference(resolution,[],[f271,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f271,plain,
    ( m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl4_4
    | spl4_19
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f267,f67,f270,f88])).

fof(f67,plain,
    ( spl4_1
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f267,plain,
    ( m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f265,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f248,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f248,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | ~ spl4_1 ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f263,plain,
    ( ~ spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f35,f258])).

fof(f258,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(resolution,[],[f255,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f255,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f249,f64])).

fof(f64,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f249,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2))
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f68,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK0
    & ( r1_tarski(sK0,k3_zfmisc_1(sK2,sK0,sK1))
      | r1_tarski(sK0,k3_zfmisc_1(sK1,sK2,sK0))
      | r1_tarski(sK0,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) )
   => ( k1_xboole_0 != sK0
      & ( r1_tarski(sK0,k3_zfmisc_1(sK2,sK0,sK1))
        | r1_tarski(sK0,k3_zfmisc_1(sK1,sK2,sK0))
        | r1_tarski(sK0,k3_zfmisc_1(sK0,sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
            & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
            & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f243,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f242,f134,f88,f95,f91])).

fof(f91,plain,
    ( spl4_5
  <=> m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( spl4_10
  <=> sK3(sK0) = k3_mcart_1(k5_mcart_1(sK2,sK0,sK1,sK3(sK0)),k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),k7_mcart_1(sK2,sK0,sK1,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f242,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | sK3(sK0) != sK3(sK0)
    | ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f204,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),X0)
        | k1_xboole_0 = X0
        | v1_xboole_0(X0)
        | sK3(X0) != sK3(sK0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f202,f41])).

fof(f202,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),X1)
        | sK3(sK0) != sK3(X1)
        | k1_xboole_0 = X1 )
    | ~ spl4_10 ),
    inference(superposition,[],[f40,f135])).

fof(f135,plain,
    ( sK3(sK0) = k3_mcart_1(k5_mcart_1(sK2,sK0,sK1,sK3(sK0)),k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),k7_mcart_1(sK2,sK0,sK1,sK3(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f40,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f196,plain,
    ( spl4_8
    | spl4_4
    | spl4_9
    | spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f195,f91,f134,f131,f88,f128])).

fof(f195,plain,
    ( sK3(sK0) = k3_mcart_1(k5_mcart_1(sK2,sK0,sK1,sK3(sK0)),k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),k7_mcart_1(sK2,sK0,sK1,sK3(sK0)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,
    ( m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f193,plain,
    ( spl4_4
    | spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f191,f73,f91,f88])).

fof(f73,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f191,plain,
    ( m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(resolution,[],[f161,f38])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f160,f47])).

fof(f160,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f74,f45])).

fof(f74,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f187,plain,
    ( ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f35,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f182,f37])).

fof(f182,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f177,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f177,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f74,f132])).

fof(f159,plain,
    ( ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f35,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(resolution,[],[f154,f37])).

fof(f154,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f153,f63])).

fof(f153,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f68,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f152,plain,
    ( ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f35,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f147,f37])).

fof(f147,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f143,f65])).

fof(f65,plain,(
    ! [X2,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0),sK1))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f74,f129])).

fof(f120,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f35,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(resolution,[],[f96,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f96,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f107,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f35,f89])).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f80,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f35,f76])).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f71,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_2
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f75,plain,
    ( spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f55,f73,f70,f67])).

fof(f55,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK0))
    | r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f34,f46,f46,f46])).

fof(f34,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(sK2,sK0,sK1))
    | r1_tarski(sK0,k3_zfmisc_1(sK1,sK2,sK0))
    | r1_tarski(sK0,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
