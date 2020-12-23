%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 153 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  234 ( 549 expanded)
%              Number of equality atoms :   49 (  84 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f197,f207,f211,f279])).

fof(f279,plain,
    ( ~ spl6_1
    | spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl6_1
    | spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f277,f195])).

fof(f195,plain,
    ( k1_xboole_0 != sK1
    | spl6_6 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f277,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_1
    | spl6_5 ),
    inference(subsumption_resolution,[],[f276,f191])).

fof(f191,plain,
    ( k1_xboole_0 != sK0
    | spl6_5 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f276,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_1 ),
    inference(superposition,[],[f47,f267])).

fof(f267,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f261,f34])).

fof(f34,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f261,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl6_1 ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_1
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f211,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f209,f74])).

fof(f74,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f209,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f34,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f194])).

fof(f207,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f206])).

% (8560)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f206,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f200,f74])).

fof(f200,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f79,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f190])).

fof(f79,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK0,X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f73,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f197,plain,
    ( spl6_5
    | spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f188,f62,f194,f190])).

fof(f62,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f188,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(superposition,[],[f47,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f153,f34])).

fof(f153,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | r1_tarski(sK1,sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f50,f64])).

fof(f64,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f33,f62,f58])).

fof(f33,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (8563)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (8574)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (8582)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (8582)Refutation not found, incomplete strategy% (8582)------------------------------
% 0.21/0.55  % (8582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8563)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (8582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (8582)Memory used [KB]: 10746
% 0.21/0.57  % (8582)Time elapsed: 0.128 s
% 0.21/0.57  % (8582)------------------------------
% 0.21/0.57  % (8582)------------------------------
% 0.21/0.57  % (8564)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (8571)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f65,f197,f207,f211,f279])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ~spl6_1 | spl6_5 | spl6_6),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    $false | (~spl6_1 | spl6_5 | spl6_6)),
% 0.21/0.57    inference(subsumption_resolution,[],[f277,f195])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    k1_xboole_0 != sK1 | spl6_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f194])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    spl6_6 <=> k1_xboole_0 = sK1),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | (~spl6_1 | spl6_5)),
% 0.21/0.57    inference(subsumption_resolution,[],[f276,f191])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | spl6_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f190])).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    spl6_5 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl6_1),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f275])).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl6_1),
% 0.21/0.57    inference(superposition,[],[f47,f267])).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f261,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.57    inference(negated_conjecture,[],[f8])).
% 0.21/0.57  fof(f8,conjecture,(
% 0.21/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.21/0.57  fof(f261,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK1,sK3) | ~spl6_1),
% 0.21/0.57    inference(resolution,[],[f51,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    spl6_1 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(flattening,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    ~spl6_6),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f210])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    $false | ~spl6_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f209,f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 0.21/0.57    inference(resolution,[],[f71,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(resolution,[],[f39,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(equality_resolution,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.57  fof(f209,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,sK3) | ~spl6_6),
% 0.21/0.57    inference(backward_demodulation,[],[f34,f196])).
% 0.21/0.57  fof(f196,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~spl6_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f194])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    ~spl6_5),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.57  % (8560)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  fof(f206,plain,(
% 0.21/0.57    $false | ~spl6_5),
% 0.21/0.57    inference(subsumption_resolution,[],[f200,f74])).
% 0.21/0.57  fof(f200,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl6_5),
% 0.21/0.57    inference(backward_demodulation,[],[f79,f192])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | ~spl6_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f190])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f73,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_xboole_0(sK0,X0) | ~r1_tarski(sK0,X0)) )),
% 0.21/0.57    inference(resolution,[],[f40,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ~v1_xboole_0(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.57    inference(resolution,[],[f71,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    spl6_5 | spl6_6 | ~spl6_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f188,f62,f194,f190])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_2),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f187])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_2),
% 0.21/0.57    inference(superposition,[],[f47,f167])).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl6_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f153,f34])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | r1_tarski(sK1,sK3) | ~spl6_2),
% 0.21/0.57    inference(resolution,[],[f50,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl6_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f62])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    spl6_1 | spl6_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f33,f62,f58])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (8563)------------------------------
% 0.21/0.57  % (8563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8563)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (8563)Memory used [KB]: 10874
% 0.21/0.57  % (8563)Time elapsed: 0.128 s
% 0.21/0.57  % (8563)------------------------------
% 0.21/0.57  % (8563)------------------------------
% 0.21/0.57  % (8565)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (8559)Success in time 0.206 s
%------------------------------------------------------------------------------
