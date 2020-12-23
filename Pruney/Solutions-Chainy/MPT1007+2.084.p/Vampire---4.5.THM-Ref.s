%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 982 expanded)
%              Number of leaves         :   31 ( 292 expanded)
%              Depth                    :   22
%              Number of atoms          :  436 (2565 expanded)
%              Number of equality atoms :  137 (1103 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f425,f427,f535,f640,f676])).

fof(f676,plain,
    ( ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f674,f167])).

fof(f167,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f164,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f93,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

% (5402)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f95,f61])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f674,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f332,f278])).

fof(f278,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f332,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl6_7
  <=> r2_hidden(sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f640,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f634,f114])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f634,plain,
    ( ! [X5] : ~ r1_tarski(sK1,X5)
    | spl6_7 ),
    inference(resolution,[],[f629,f116])).

fof(f116,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f629,plain,
    ( ! [X0] : ~ r2_hidden(sK1,X0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f628,f61])).

fof(f628,plain,
    ( ! [X0] :
        ( k5_xboole_0(X0,k1_xboole_0) != X0
        | ~ r2_hidden(sK1,X0) )
    | spl6_7 ),
    inference(forward_demodulation,[],[f626,f172])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f168,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f168,plain,(
    ! [X2,X3] : ~ r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f163,f149])).

fof(f149,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0))
      | ~ r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0)) ) ),
    inference(superposition,[],[f93,f109])).

fof(f109,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f163,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0)) ) ),
    inference(superposition,[],[f95,f109])).

fof(f626,plain,
    ( ! [X0] :
        ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) != X0
        | ~ r2_hidden(sK1,X0) )
    | spl6_7 ),
    inference(superposition,[],[f111,f625])).

fof(f625,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl6_7 ),
    inference(forward_demodulation,[],[f624,f59])).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f624,plain,
    ( k1_relat_1(k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl6_7 ),
    inference(forward_demodulation,[],[f239,f341])).

fof(f341,plain,
    ( k1_xboole_0 = sK3
    | spl6_7 ),
    inference(resolution,[],[f333,f64])).

fof(f333,plain,
    ( ~ r2_hidden(sK4(sK3),sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f331])).

fof(f239,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f238,f190])).

fof(f190,plain,(
    k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f82,f107])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f56,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f96,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f98,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f99,f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f238,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(subsumption_resolution,[],[f237,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f237,plain,
    ( k1_xboole_0 = sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(subsumption_resolution,[],[f236,f108])).

fof(f108,plain,(
    v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f55,f106])).

fof(f55,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f236,plain,
    ( ~ v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
    | k1_xboole_0 = sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(resolution,[],[f83,f141])).

fof(f141,plain,(
    sP0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3,sK2) ),
    inference(resolution,[],[f107,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f77,f68,f106])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f535,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f329,f280,f335,f331])).

fof(f335,plain,
    ( spl6_8
  <=> r2_hidden(sK1,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f280,plain,
    ( spl6_6
  <=> sK1 = k1_mcart_1(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f329,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3))
    | ~ r2_hidden(sK4(sK3),sK3)
    | ~ spl6_6 ),
    inference(superposition,[],[f243,f282])).

fof(f282,plain,
    ( sK1 = k1_mcart_1(sK4(sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f280])).

fof(f243,plain,(
    ! [X1] :
      ( r2_hidden(k1_mcart_1(X1),k1_relat_1(sK3))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(backward_demodulation,[],[f228,f239])).

fof(f228,plain,(
    ! [X1] :
      ( r2_hidden(k1_mcart_1(X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f142,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f142,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f427,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f314,f280,f276])).

fof(f314,plain,
    ( sK1 = k1_mcart_1(sK4(sK3))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f265,f64])).

fof(f265,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | k1_mcart_1(X0) = sK1 ) ),
    inference(resolution,[],[f263,f244])).

fof(f244,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK3),sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(backward_demodulation,[],[f142,f239])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK3),X1))
      | k1_mcart_1(X0) = sK1 ) ),
    inference(superposition,[],[f113,f239])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f90,f106])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f425,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f423,f337])).

fof(f337,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f335])).

fof(f423,plain,(
    ~ r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(resolution,[],[f412,f58])).

fof(f58,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f412,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f411,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f411,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X0),sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f410,f248])).

fof(f248,plain,(
    v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f108,f239])).

fof(f410,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X0),sK2)
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f406,f57])).

fof(f406,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X0),sK2)
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f247,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

% (5415)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f247,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(backward_demodulation,[],[f107,f239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.54  % (5404)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (5405)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (5421)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (5420)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (5413)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (5412)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (5407)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (5412)Refutation not found, incomplete strategy% (5412)------------------------------
% 0.22/0.56  % (5412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (5404)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (5412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (5412)Memory used [KB]: 1791
% 0.22/0.58  % (5412)Time elapsed: 0.126 s
% 0.22/0.58  % (5412)------------------------------
% 0.22/0.58  % (5412)------------------------------
% 1.44/0.58  % SZS output start Proof for theBenchmark
% 1.44/0.58  fof(f677,plain,(
% 1.44/0.58    $false),
% 1.44/0.58    inference(avatar_sat_refutation,[],[f425,f427,f535,f640,f676])).
% 1.44/0.58  fof(f676,plain,(
% 1.44/0.58    ~spl6_5 | ~spl6_7),
% 1.44/0.58    inference(avatar_contradiction_clause,[],[f675])).
% 1.44/0.58  fof(f675,plain,(
% 1.44/0.58    $false | (~spl6_5 | ~spl6_7)),
% 1.44/0.58    inference(subsumption_resolution,[],[f674,f167])).
% 1.44/0.58  fof(f167,plain,(
% 1.44/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f164,f150])).
% 1.44/0.58  fof(f150,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.44/0.58    inference(duplicate_literal_removal,[],[f147])).
% 1.44/0.58  fof(f147,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.44/0.58    inference(superposition,[],[f93,f61])).
% 1.44/0.58  fof(f61,plain,(
% 1.44/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f5])).
% 1.44/0.58  % (5402)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.44/0.58  fof(f5,axiom,(
% 1.44/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.58  fof(f93,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f53])).
% 1.44/0.58  fof(f53,plain,(
% 1.44/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.44/0.58    inference(nnf_transformation,[],[f34])).
% 1.44/0.58  fof(f34,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.44/0.58    inference(ennf_transformation,[],[f1])).
% 1.44/0.58  fof(f1,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.44/0.58  fof(f164,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.44/0.58    inference(duplicate_literal_removal,[],[f161])).
% 1.44/0.58  fof(f161,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.44/0.58    inference(superposition,[],[f95,f61])).
% 1.44/0.58  fof(f95,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f53])).
% 1.44/0.58  fof(f674,plain,(
% 1.44/0.58    r2_hidden(sK4(k1_xboole_0),k1_xboole_0) | (~spl6_5 | ~spl6_7)),
% 1.44/0.58    inference(forward_demodulation,[],[f332,f278])).
% 1.44/0.58  fof(f278,plain,(
% 1.44/0.58    k1_xboole_0 = sK3 | ~spl6_5),
% 1.44/0.58    inference(avatar_component_clause,[],[f276])).
% 1.44/0.58  fof(f276,plain,(
% 1.44/0.58    spl6_5 <=> k1_xboole_0 = sK3),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.44/0.58  fof(f332,plain,(
% 1.44/0.58    r2_hidden(sK4(sK3),sK3) | ~spl6_7),
% 1.44/0.58    inference(avatar_component_clause,[],[f331])).
% 1.44/0.58  fof(f331,plain,(
% 1.44/0.58    spl6_7 <=> r2_hidden(sK4(sK3),sK3)),
% 1.44/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.44/0.58  fof(f640,plain,(
% 1.44/0.58    spl6_7),
% 1.44/0.58    inference(avatar_contradiction_clause,[],[f639])).
% 1.44/0.58  fof(f639,plain,(
% 1.44/0.58    $false | spl6_7),
% 1.44/0.58    inference(resolution,[],[f634,f114])).
% 1.44/0.58  fof(f114,plain,(
% 1.44/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.58    inference(equality_resolution,[],[f71])).
% 1.44/0.58  fof(f71,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.58    inference(cnf_transformation,[],[f44])).
% 1.44/0.58  fof(f44,plain,(
% 1.44/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.58    inference(flattening,[],[f43])).
% 1.44/0.58  fof(f43,plain,(
% 1.44/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.58    inference(nnf_transformation,[],[f2])).
% 1.44/0.58  fof(f2,axiom,(
% 1.44/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.58  fof(f634,plain,(
% 1.44/0.58    ( ! [X5] : (~r1_tarski(sK1,X5)) ) | spl6_7),
% 1.44/0.58    inference(resolution,[],[f629,f116])).
% 1.44/0.58  fof(f116,plain,(
% 1.44/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.44/0.58    inference(equality_resolution,[],[f74])).
% 1.44/0.58  fof(f74,plain,(
% 1.44/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.58    inference(cnf_transformation,[],[f48])).
% 1.44/0.58  fof(f48,plain,(
% 1.44/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 1.44/0.58  fof(f47,plain,(
% 1.44/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.44/0.58    introduced(choice_axiom,[])).
% 1.44/0.58  fof(f46,plain,(
% 1.44/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.58    inference(rectify,[],[f45])).
% 1.44/0.58  fof(f45,plain,(
% 1.44/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.58    inference(nnf_transformation,[],[f13])).
% 1.44/0.58  fof(f13,axiom,(
% 1.44/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.44/0.58  fof(f629,plain,(
% 1.44/0.58    ( ! [X0] : (~r2_hidden(sK1,X0)) ) | spl6_7),
% 1.44/0.58    inference(subsumption_resolution,[],[f628,f61])).
% 1.44/0.58  fof(f628,plain,(
% 1.44/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) != X0 | ~r2_hidden(sK1,X0)) ) | spl6_7),
% 1.44/0.58    inference(forward_demodulation,[],[f626,f172])).
% 1.44/0.58  fof(f172,plain,(
% 1.44/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.58    inference(resolution,[],[f168,f64])).
% 1.44/0.58  fof(f64,plain,(
% 1.44/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f42])).
% 1.44/0.58  fof(f42,plain,(
% 1.44/0.58    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.44/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f41])).
% 1.44/0.58  fof(f41,plain,(
% 1.44/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.44/0.58    introduced(choice_axiom,[])).
% 1.44/0.58  fof(f27,plain,(
% 1.44/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.44/0.58    inference(ennf_transformation,[],[f20])).
% 1.44/0.58  fof(f20,axiom,(
% 1.44/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.44/0.58  fof(f168,plain,(
% 1.44/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0))) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f163,f149])).
% 1.44/0.58  fof(f149,plain,(
% 1.44/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0)) | ~r2_hidden(X3,X2)) )),
% 1.44/0.58    inference(duplicate_literal_removal,[],[f148])).
% 1.44/0.58  fof(f148,plain,(
% 1.44/0.58    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0))) )),
% 1.44/0.58    inference(superposition,[],[f93,f109])).
% 1.44/0.58  fof(f109,plain,(
% 1.44/0.58    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.44/0.58    inference(definition_unfolding,[],[f62,f68])).
% 1.44/0.58  fof(f68,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f3])).
% 1.44/0.58  fof(f3,axiom,(
% 1.44/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.58  fof(f62,plain,(
% 1.44/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f4])).
% 1.44/0.58  fof(f4,axiom,(
% 1.44/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.44/0.58  fof(f163,plain,(
% 1.44/0.58    ( ! [X2,X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0))) )),
% 1.44/0.58    inference(duplicate_literal_removal,[],[f162])).
% 1.44/0.58  fof(f162,plain,(
% 1.44/0.58    ( ! [X2,X3] : (r2_hidden(X3,X2) | r2_hidden(X3,X2) | ~r2_hidden(X3,k3_xboole_0(X2,k1_xboole_0))) )),
% 1.44/0.58    inference(superposition,[],[f95,f109])).
% 1.44/0.58  fof(f626,plain,(
% 1.44/0.58    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) != X0 | ~r2_hidden(sK1,X0)) ) | spl6_7),
% 1.44/0.58    inference(superposition,[],[f111,f625])).
% 1.44/0.58  fof(f625,plain,(
% 1.44/0.58    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | spl6_7),
% 1.44/0.58    inference(forward_demodulation,[],[f624,f59])).
% 1.44/0.58  fof(f59,plain,(
% 1.44/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.58    inference(cnf_transformation,[],[f16])).
% 1.44/0.58  fof(f16,axiom,(
% 1.44/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.44/0.58  fof(f624,plain,(
% 1.44/0.58    k1_relat_1(k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | spl6_7),
% 1.44/0.58    inference(forward_demodulation,[],[f239,f341])).
% 1.44/0.58  fof(f341,plain,(
% 1.44/0.58    k1_xboole_0 = sK3 | spl6_7),
% 1.44/0.58    inference(resolution,[],[f333,f64])).
% 1.44/0.58  fof(f333,plain,(
% 1.44/0.58    ~r2_hidden(sK4(sK3),sK3) | spl6_7),
% 1.44/0.58    inference(avatar_component_clause,[],[f331])).
% 1.44/0.58  fof(f239,plain,(
% 1.44/0.58    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK3)),
% 1.44/0.58    inference(forward_demodulation,[],[f238,f190])).
% 1.44/0.58  fof(f190,plain,(
% 1.44/0.58    k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3)),
% 1.44/0.58    inference(resolution,[],[f82,f107])).
% 1.44/0.58  fof(f107,plain,(
% 1.44/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 1.44/0.58    inference(definition_unfolding,[],[f56,f106])).
% 1.44/0.58  fof(f106,plain,(
% 1.44/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f63,f105])).
% 1.44/0.58  fof(f105,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f67,f104])).
% 1.44/0.58  fof(f104,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f79,f103])).
% 1.44/0.58  fof(f103,plain,(
% 1.44/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f96,f102])).
% 1.44/0.58  fof(f102,plain,(
% 1.44/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f98,f101])).
% 1.44/0.58  fof(f101,plain,(
% 1.44/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f99,f100])).
% 1.44/0.58  fof(f100,plain,(
% 1.44/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f12])).
% 1.44/0.58  fof(f12,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.44/0.58  fof(f99,plain,(
% 1.44/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f11])).
% 1.44/0.58  fof(f11,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.44/0.58  fof(f98,plain,(
% 1.44/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f10])).
% 1.44/0.58  fof(f10,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.44/0.58  fof(f96,plain,(
% 1.44/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f9])).
% 1.44/0.58  fof(f9,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.58  fof(f79,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f8])).
% 1.44/0.58  fof(f8,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.58  fof(f67,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f7])).
% 1.44/0.58  fof(f7,axiom,(
% 1.44/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.58  fof(f63,plain,(
% 1.44/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f6])).
% 1.44/0.58  fof(f6,axiom,(
% 1.44/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.58  fof(f56,plain,(
% 1.44/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.44/0.58    inference(cnf_transformation,[],[f40])).
% 1.44/0.58  fof(f40,plain,(
% 1.44/0.58    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.44/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f39])).
% 1.44/0.58  fof(f39,plain,(
% 1.44/0.58    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.44/0.58    introduced(choice_axiom,[])).
% 1.44/0.58  fof(f26,plain,(
% 1.44/0.58    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.44/0.58    inference(flattening,[],[f25])).
% 1.44/0.58  fof(f25,plain,(
% 1.44/0.58    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.44/0.58    inference(ennf_transformation,[],[f24])).
% 1.44/0.58  fof(f24,negated_conjecture,(
% 1.44/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.44/0.58    inference(negated_conjecture,[],[f23])).
% 1.44/0.58  fof(f23,conjecture,(
% 1.44/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 1.44/0.58  fof(f82,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f30])).
% 1.44/0.58  fof(f30,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f17])).
% 1.44/0.58  fof(f17,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.44/0.58  fof(f238,plain,(
% 1.44/0.58    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3)),
% 1.44/0.58    inference(subsumption_resolution,[],[f237,f57])).
% 1.44/0.58  fof(f57,plain,(
% 1.44/0.58    k1_xboole_0 != sK2),
% 1.44/0.58    inference(cnf_transformation,[],[f40])).
% 1.44/0.58  fof(f237,plain,(
% 1.44/0.58    k1_xboole_0 = sK2 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3)),
% 1.44/0.58    inference(subsumption_resolution,[],[f236,f108])).
% 1.44/0.58  fof(f108,plain,(
% 1.44/0.58    v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.44/0.58    inference(definition_unfolding,[],[f55,f106])).
% 1.44/0.58  fof(f55,plain,(
% 1.44/0.58    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.44/0.58    inference(cnf_transformation,[],[f40])).
% 1.44/0.58  fof(f236,plain,(
% 1.44/0.58    ~v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) | k1_xboole_0 = sK2 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3)),
% 1.44/0.58    inference(resolution,[],[f83,f141])).
% 1.44/0.58  fof(f141,plain,(
% 1.44/0.58    sP0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3,sK2)),
% 1.44/0.58    inference(resolution,[],[f107,f87])).
% 1.44/0.59  fof(f87,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f52])).
% 1.44/0.59  fof(f52,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.59    inference(nnf_transformation,[],[f38])).
% 1.44/0.59  fof(f38,plain,(
% 1.44/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.59    inference(definition_folding,[],[f32,f37])).
% 1.44/0.59  fof(f37,plain,(
% 1.44/0.59    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.44/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.59  fof(f32,plain,(
% 1.44/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.59    inference(flattening,[],[f31])).
% 1.44/0.59  fof(f31,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.59    inference(ennf_transformation,[],[f21])).
% 1.44/0.59  fof(f21,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.44/0.59  fof(f83,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.44/0.59    inference(cnf_transformation,[],[f51])).
% 1.44/0.59  fof(f51,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.44/0.59    inference(rectify,[],[f50])).
% 1.44/0.59  fof(f50,plain,(
% 1.44/0.59    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.44/0.59    inference(nnf_transformation,[],[f37])).
% 1.44/0.59  fof(f111,plain,(
% 1.44/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != X0 | ~r2_hidden(X1,X0)) )),
% 1.44/0.59    inference(definition_unfolding,[],[f77,f68,f106])).
% 1.44/0.59  fof(f77,plain,(
% 1.44/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.44/0.59    inference(cnf_transformation,[],[f49])).
% 1.44/0.59  fof(f49,plain,(
% 1.44/0.59    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.44/0.59    inference(nnf_transformation,[],[f14])).
% 1.44/0.59  fof(f14,axiom,(
% 1.44/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.44/0.59  fof(f535,plain,(
% 1.44/0.59    ~spl6_7 | spl6_8 | ~spl6_6),
% 1.44/0.59    inference(avatar_split_clause,[],[f329,f280,f335,f331])).
% 1.44/0.59  fof(f335,plain,(
% 1.44/0.59    spl6_8 <=> r2_hidden(sK1,k1_relat_1(sK3))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.44/0.59  fof(f280,plain,(
% 1.44/0.59    spl6_6 <=> sK1 = k1_mcart_1(sK4(sK3))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.44/0.59  fof(f329,plain,(
% 1.44/0.59    r2_hidden(sK1,k1_relat_1(sK3)) | ~r2_hidden(sK4(sK3),sK3) | ~spl6_6),
% 1.44/0.59    inference(superposition,[],[f243,f282])).
% 1.44/0.59  fof(f282,plain,(
% 1.44/0.59    sK1 = k1_mcart_1(sK4(sK3)) | ~spl6_6),
% 1.44/0.59    inference(avatar_component_clause,[],[f280])).
% 1.44/0.59  fof(f243,plain,(
% 1.44/0.59    ( ! [X1] : (r2_hidden(k1_mcart_1(X1),k1_relat_1(sK3)) | ~r2_hidden(X1,sK3)) )),
% 1.44/0.59    inference(backward_demodulation,[],[f228,f239])).
% 1.44/0.59  fof(f228,plain,(
% 1.44/0.59    ( ! [X1] : (r2_hidden(k1_mcart_1(X1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X1,sK3)) )),
% 1.44/0.59    inference(resolution,[],[f142,f80])).
% 1.44/0.59  fof(f80,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f29])).
% 1.44/0.59  fof(f29,plain,(
% 1.44/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.44/0.59    inference(ennf_transformation,[],[f18])).
% 1.44/0.59  fof(f18,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.44/0.59  fof(f142,plain,(
% 1.44/0.59    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) | ~r2_hidden(X0,sK3)) )),
% 1.44/0.59    inference(resolution,[],[f107,f69])).
% 1.44/0.59  fof(f69,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f28])).
% 1.44/0.59  fof(f28,plain,(
% 1.44/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.59    inference(ennf_transformation,[],[f15])).
% 1.44/0.59  fof(f15,axiom,(
% 1.44/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.44/0.59  fof(f427,plain,(
% 1.44/0.59    spl6_5 | spl6_6),
% 1.44/0.59    inference(avatar_split_clause,[],[f314,f280,f276])).
% 1.44/0.59  fof(f314,plain,(
% 1.44/0.59    sK1 = k1_mcart_1(sK4(sK3)) | k1_xboole_0 = sK3),
% 1.44/0.59    inference(resolution,[],[f265,f64])).
% 1.44/0.59  fof(f265,plain,(
% 1.44/0.59    ( ! [X0] : (~r2_hidden(X0,sK3) | k1_mcart_1(X0) = sK1) )),
% 1.44/0.59    inference(resolution,[],[f263,f244])).
% 1.44/0.59  fof(f244,plain,(
% 1.44/0.59    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK3),sK2)) | ~r2_hidden(X0,sK3)) )),
% 1.44/0.59    inference(backward_demodulation,[],[f142,f239])).
% 1.44/0.59  fof(f263,plain,(
% 1.44/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK3),X1)) | k1_mcart_1(X0) = sK1) )),
% 1.44/0.59    inference(superposition,[],[f113,f239])).
% 1.44/0.59  fof(f113,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.44/0.59    inference(definition_unfolding,[],[f90,f106])).
% 1.44/0.59  fof(f90,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 1.44/0.59    inference(cnf_transformation,[],[f33])).
% 1.44/0.59  fof(f33,plain,(
% 1.44/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.44/0.59    inference(ennf_transformation,[],[f19])).
% 1.44/0.59  fof(f19,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.44/0.59  fof(f425,plain,(
% 1.44/0.59    ~spl6_8),
% 1.44/0.59    inference(avatar_contradiction_clause,[],[f424])).
% 1.44/0.59  fof(f424,plain,(
% 1.44/0.59    $false | ~spl6_8),
% 1.44/0.59    inference(subsumption_resolution,[],[f423,f337])).
% 1.44/0.59  fof(f337,plain,(
% 1.44/0.59    r2_hidden(sK1,k1_relat_1(sK3)) | ~spl6_8),
% 1.44/0.59    inference(avatar_component_clause,[],[f335])).
% 1.44/0.59  fof(f423,plain,(
% 1.44/0.59    ~r2_hidden(sK1,k1_relat_1(sK3))),
% 1.44/0.59    inference(resolution,[],[f412,f58])).
% 1.44/0.59  fof(f58,plain,(
% 1.44/0.59    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 1.44/0.59    inference(cnf_transformation,[],[f40])).
% 1.44/0.59  fof(f412,plain,(
% 1.44/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK2) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.44/0.59    inference(subsumption_resolution,[],[f411,f54])).
% 1.44/0.59  fof(f54,plain,(
% 1.44/0.59    v1_funct_1(sK3)),
% 1.44/0.59    inference(cnf_transformation,[],[f40])).
% 1.44/0.59  fof(f411,plain,(
% 1.44/0.59    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),sK2) | ~v1_funct_1(sK3)) )),
% 1.44/0.59    inference(subsumption_resolution,[],[f410,f248])).
% 1.44/0.59  fof(f248,plain,(
% 1.44/0.59    v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.44/0.59    inference(backward_demodulation,[],[f108,f239])).
% 1.44/0.59  fof(f410,plain,(
% 1.44/0.59    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),sK2) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) )),
% 1.44/0.59    inference(subsumption_resolution,[],[f406,f57])).
% 1.44/0.59  fof(f406,plain,(
% 1.44/0.59    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),sK2) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) )),
% 1.44/0.59    inference(resolution,[],[f247,f97])).
% 1.44/0.59  fof(f97,plain,(
% 1.44/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f36])).
% 1.44/0.59  fof(f36,plain,(
% 1.44/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.44/0.59    inference(flattening,[],[f35])).
% 1.44/0.59  fof(f35,plain,(
% 1.44/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.44/0.59    inference(ennf_transformation,[],[f22])).
% 1.44/0.59  % (5415)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.59  fof(f22,axiom,(
% 1.44/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.44/0.59  fof(f247,plain,(
% 1.44/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.44/0.59    inference(backward_demodulation,[],[f107,f239])).
% 1.44/0.59  % SZS output end Proof for theBenchmark
% 1.44/0.59  % (5404)------------------------------
% 1.44/0.59  % (5404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (5404)Termination reason: Refutation
% 1.44/0.59  
% 1.44/0.59  % (5404)Memory used [KB]: 11129
% 1.44/0.59  % (5404)Time elapsed: 0.148 s
% 1.44/0.59  % (5404)------------------------------
% 1.44/0.59  % (5404)------------------------------
% 1.44/0.59  % (5421)Refutation not found, incomplete strategy% (5421)------------------------------
% 1.44/0.59  % (5421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (5421)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.59  
% 1.44/0.59  % (5421)Memory used [KB]: 10874
% 1.44/0.59  % (5421)Time elapsed: 0.137 s
% 1.44/0.59  % (5421)------------------------------
% 1.44/0.59  % (5421)------------------------------
% 1.44/0.59  % (5397)Success in time 0.217 s
%------------------------------------------------------------------------------
