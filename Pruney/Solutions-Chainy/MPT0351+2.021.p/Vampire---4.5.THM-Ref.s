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
% DateTime   : Thu Dec  3 12:44:06 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 527 expanded)
%              Number of leaves         :   20 ( 162 expanded)
%              Depth                    :   19
%              Number of atoms          :  213 ( 901 expanded)
%              Number of equality atoms :   72 ( 463 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f163,f379,f384])).

fof(f384,plain,
    ( spl3_1
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f374,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f374,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f239,f346])).

fof(f346,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f128,f345])).

fof(f345,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f343,f102])).

fof(f102,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f99,f53])).

fof(f53,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f99,plain,(
    ! [X4] : k3_tarski(k1_enumset1(X4,X4,X4)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f56,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f55,f53])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f38,f41,f52])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f42,f52,f41])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f343,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f341,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

% (2272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f139,plain,
    ( spl3_6
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f341,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(resolution,[],[f214,f221])).

fof(f221,plain,
    ( ! [X5] :
        ( r2_hidden(sK2(sK1,X5),sK0)
        | k3_tarski(k1_enumset1(X5,X5,sK1)) = X5 )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f220,f102])).

fof(f220,plain,
    ( ! [X5] :
        ( k3_tarski(k1_enumset1(X5,X5,sK1)) = k5_xboole_0(X5,k1_xboole_0)
        | r2_hidden(sK2(sK1,X5),sK0) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f216,f141])).

fof(f216,plain,(
    ! [X5] :
      ( k3_tarski(k1_enumset1(X5,X5,sK1)) = k5_xboole_0(X5,k5_xboole_0(sK1,sK1))
      | r2_hidden(sK2(sK1,X5),sK0) ) ),
    inference(resolution,[],[f96,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r2_hidden(sK2(sK1,X0),sK0) ) ),
    inference(resolution,[],[f79,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,X0)) ) ),
    inference(superposition,[],[f56,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f214,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(X2,X1),X1)
      | k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X2)) ) ),
    inference(resolution,[],[f96,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,(
    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f125,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

% (2285)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k1_enumset1(X0,X0,sK1)) ) ),
    inference(resolution,[],[f57,f32])).

% (2274)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f239,plain,
    ( ~ r1_tarski(sK0,k4_subset_1(sK0,sK0,sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f69,f236])).

fof(f236,plain,(
    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f235,f128])).

fof(f235,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f233,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f233,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f126,f32])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k3_tarski(k1_enumset1(X2,X2,X1)) = k4_subset_1(X1,X2,X1) ) ),
    inference(resolution,[],[f57,f61])).

fof(f69,plain,
    ( ~ r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f379,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f362,f58])).

fof(f362,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_2
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f240,f346])).

fof(f240,plain,
    ( ~ r1_tarski(k4_subset_1(sK0,sK0,sK1),sK0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f73,f236])).

fof(f73,plain,
    ( ~ r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_2
  <=> r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f163,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f148,f58])).

fof(f148,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_6 ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK1,sK1)
    | spl3_6 ),
    inference(superposition,[],[f140,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f82,f43])).

fof(f140,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f75,plain,
    ( ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f63,f67,f71])).

fof(f63,plain,
    ( ~ r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0))
    | ~ r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0) ),
    inference(extensionality_resolution,[],[f47,f60])).

fof(f60,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:59:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (2289)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (2278)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (2281)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (2275)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (2295)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (2270)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (2270)Refutation not found, incomplete strategy% (2270)------------------------------
% 0.21/0.51  % (2270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2270)Memory used [KB]: 6140
% 0.21/0.51  % (2270)Time elapsed: 0.112 s
% 0.21/0.51  % (2270)------------------------------
% 0.21/0.51  % (2270)------------------------------
% 0.21/0.51  % (2269)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (2275)Refutation not found, incomplete strategy% (2275)------------------------------
% 0.21/0.51  % (2275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2277)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (2275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2275)Memory used [KB]: 10618
% 0.21/0.51  % (2275)Time elapsed: 0.069 s
% 0.21/0.51  % (2275)------------------------------
% 0.21/0.51  % (2275)------------------------------
% 0.21/0.51  % (2267)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (2277)Refutation not found, incomplete strategy% (2277)------------------------------
% 0.21/0.51  % (2277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2271)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2287)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (2268)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (2283)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (2294)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (2277)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2277)Memory used [KB]: 10746
% 0.21/0.52  % (2277)Time elapsed: 0.111 s
% 0.21/0.52  % (2277)------------------------------
% 0.21/0.52  % (2277)------------------------------
% 0.21/0.52  % (2290)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (2286)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (2266)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (2266)Refutation not found, incomplete strategy% (2266)------------------------------
% 0.21/0.53  % (2266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2266)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2266)Memory used [KB]: 1663
% 0.21/0.53  % (2266)Time elapsed: 0.126 s
% 0.21/0.53  % (2266)------------------------------
% 0.21/0.53  % (2266)------------------------------
% 1.34/0.53  % (2287)Refutation not found, incomplete strategy% (2287)------------------------------
% 1.34/0.53  % (2287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (2271)Refutation not found, incomplete strategy% (2271)------------------------------
% 1.34/0.53  % (2271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (2271)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (2271)Memory used [KB]: 6268
% 1.34/0.53  % (2271)Time elapsed: 0.128 s
% 1.34/0.53  % (2271)------------------------------
% 1.34/0.53  % (2271)------------------------------
% 1.34/0.53  % (2287)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (2287)Memory used [KB]: 10746
% 1.34/0.53  % (2287)Time elapsed: 0.125 s
% 1.34/0.53  % (2287)------------------------------
% 1.34/0.53  % (2287)------------------------------
% 1.34/0.53  % (2293)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.53  % (2292)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.53  % (2273)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.53  % (2288)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.53  % (2278)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f385,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f75,f163,f379,f384])).
% 1.34/0.53  fof(f384,plain,(
% 1.34/0.53    spl3_1 | ~spl3_6),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f382])).
% 1.34/0.53  fof(f382,plain,(
% 1.34/0.53    $false | (spl3_1 | ~spl3_6)),
% 1.34/0.53    inference(resolution,[],[f374,f58])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.53    inference(equality_resolution,[],[f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(flattening,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(nnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.53  fof(f374,plain,(
% 1.34/0.53    ~r1_tarski(sK0,sK0) | (spl3_1 | ~spl3_6)),
% 1.34/0.53    inference(forward_demodulation,[],[f239,f346])).
% 1.34/0.53  fof(f346,plain,(
% 1.34/0.53    sK0 = k4_subset_1(sK0,sK0,sK1) | ~spl3_6),
% 1.34/0.53    inference(backward_demodulation,[],[f128,f345])).
% 1.34/0.53  fof(f345,plain,(
% 1.34/0.53    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_6),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f344])).
% 1.34/0.53  fof(f344,plain,(
% 1.34/0.53    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_6),
% 1.34/0.53    inference(forward_demodulation,[],[f343,f102])).
% 1.34/0.53  fof(f102,plain,(
% 1.34/0.53    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.34/0.53    inference(forward_demodulation,[],[f99,f53])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.34/0.53    inference(definition_unfolding,[],[f36,f52])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f40,f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.34/0.53    inference(rectify,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.34/0.53  fof(f99,plain,(
% 1.34/0.53    ( ! [X4] : (k3_tarski(k1_enumset1(X4,X4,X4)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.34/0.53    inference(superposition,[],[f56,f82])).
% 1.34/0.53  fof(f82,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.34/0.53    inference(superposition,[],[f55,f53])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f38,f41,f52])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f42,f52,f41])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.34/0.53  fof(f343,plain,(
% 1.34/0.53    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_6),
% 1.34/0.53    inference(forward_demodulation,[],[f341,f141])).
% 1.34/0.53  fof(f141,plain,(
% 1.34/0.53    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl3_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f139])).
% 1.34/0.53  % (2272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  fof(f139,plain,(
% 1.34/0.53    spl3_6 <=> k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.34/0.53  fof(f341,plain,(
% 1.34/0.53    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_6),
% 1.34/0.53    inference(resolution,[],[f214,f221])).
% 1.34/0.53  fof(f221,plain,(
% 1.34/0.53    ( ! [X5] : (r2_hidden(sK2(sK1,X5),sK0) | k3_tarski(k1_enumset1(X5,X5,sK1)) = X5) ) | ~spl3_6),
% 1.34/0.53    inference(forward_demodulation,[],[f220,f102])).
% 1.34/0.53  fof(f220,plain,(
% 1.34/0.53    ( ! [X5] : (k3_tarski(k1_enumset1(X5,X5,sK1)) = k5_xboole_0(X5,k1_xboole_0) | r2_hidden(sK2(sK1,X5),sK0)) ) | ~spl3_6),
% 1.34/0.53    inference(forward_demodulation,[],[f216,f141])).
% 1.34/0.53  fof(f216,plain,(
% 1.34/0.53    ( ! [X5] : (k3_tarski(k1_enumset1(X5,X5,sK1)) = k5_xboole_0(X5,k5_xboole_0(sK1,sK1)) | r2_hidden(sK2(sK1,X5),sK0)) )),
% 1.34/0.53    inference(resolution,[],[f96,f92])).
% 1.34/0.53  fof(f92,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK2(sK1,X0),sK0)) )),
% 1.34/0.53    inference(resolution,[],[f79,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.34/0.53    inference(negated_conjecture,[],[f15])).
% 1.34/0.53  fof(f15,conjecture,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.34/0.53  fof(f79,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(resolution,[],[f44,f49])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(rectify,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(nnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.34/0.53  fof(f96,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,X0))) )),
% 1.34/0.53    inference(superposition,[],[f56,f43])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.34/0.53  fof(f214,plain,(
% 1.34/0.53    ( ! [X2,X1] : (~r2_hidden(sK2(X2,X1),X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X2))) )),
% 1.34/0.53    inference(resolution,[],[f96,f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  fof(f128,plain,(
% 1.34/0.53    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.34/0.53    inference(resolution,[],[f125,f61])).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.34/0.53    inference(forward_demodulation,[],[f35,f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.34/0.53  % (2285)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.53  fof(f125,plain,(
% 1.34/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k1_enumset1(X0,X0,sK1))) )),
% 1.34/0.53    inference(resolution,[],[f57,f32])).
% 1.34/0.53  % (2274)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f51,f52])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.53    inference(flattening,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(ennf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.34/0.53  fof(f239,plain,(
% 1.34/0.53    ~r1_tarski(sK0,k4_subset_1(sK0,sK0,sK1)) | spl3_1),
% 1.34/0.53    inference(backward_demodulation,[],[f69,f236])).
% 1.34/0.53  fof(f236,plain,(
% 1.34/0.53    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.34/0.53    inference(forward_demodulation,[],[f235,f128])).
% 1.34/0.53  fof(f235,plain,(
% 1.34/0.53    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.34/0.53    inference(forward_demodulation,[],[f233,f54])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f37,f39,f39])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.34/0.53  fof(f233,plain,(
% 1.34/0.53    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 1.34/0.53    inference(resolution,[],[f126,f32])).
% 1.34/0.53  fof(f126,plain,(
% 1.34/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k3_tarski(k1_enumset1(X2,X2,X1)) = k4_subset_1(X1,X2,X1)) )),
% 1.34/0.53    inference(resolution,[],[f57,f61])).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    ~r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0)) | spl3_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f67])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    spl3_1 <=> r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.34/0.53  fof(f379,plain,(
% 1.34/0.53    spl3_2 | ~spl3_6),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f377])).
% 1.34/0.53  fof(f377,plain,(
% 1.34/0.53    $false | (spl3_2 | ~spl3_6)),
% 1.34/0.53    inference(resolution,[],[f362,f58])).
% 1.34/0.53  fof(f362,plain,(
% 1.34/0.53    ~r1_tarski(sK0,sK0) | (spl3_2 | ~spl3_6)),
% 1.34/0.53    inference(backward_demodulation,[],[f240,f346])).
% 1.34/0.53  fof(f240,plain,(
% 1.34/0.53    ~r1_tarski(k4_subset_1(sK0,sK0,sK1),sK0) | spl3_2),
% 1.34/0.53    inference(backward_demodulation,[],[f73,f236])).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    ~r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0) | spl3_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f71])).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    spl3_2 <=> r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.34/0.53  fof(f163,plain,(
% 1.34/0.53    spl3_6),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f161])).
% 1.34/0.53  fof(f161,plain,(
% 1.34/0.53    $false | spl3_6),
% 1.34/0.53    inference(resolution,[],[f148,f58])).
% 1.34/0.53  fof(f148,plain,(
% 1.34/0.53    ~r1_tarski(sK1,sK1) | spl3_6),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f147])).
% 1.34/0.53  fof(f147,plain,(
% 1.34/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK1,sK1) | spl3_6),
% 1.34/0.53    inference(superposition,[],[f140,f84])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.34/0.53    inference(superposition,[],[f82,f43])).
% 1.34/0.53  fof(f140,plain,(
% 1.34/0.53    k1_xboole_0 != k5_xboole_0(sK1,sK1) | spl3_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f139])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    ~spl3_2 | ~spl3_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f63,f67,f71])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    ~r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0)) | ~r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0)),
% 1.34/0.53    inference(extensionality_resolution,[],[f47,f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.34/0.53    inference(backward_demodulation,[],[f33,f34])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (2278)------------------------------
% 1.34/0.54  % (2278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (2278)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (2278)Memory used [KB]: 6396
% 1.34/0.54  % (2278)Time elapsed: 0.118 s
% 1.34/0.54  % (2278)------------------------------
% 1.34/0.54  % (2278)------------------------------
% 1.34/0.54  % (2282)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (2265)Success in time 0.175 s
%------------------------------------------------------------------------------
