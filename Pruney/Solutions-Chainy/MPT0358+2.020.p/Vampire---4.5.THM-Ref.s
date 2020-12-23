%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 235 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   19
%              Number of atoms          :  332 ( 808 expanded)
%              Number of equality atoms :   65 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4701)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f80,f178,f197,f258,f287,f391])).

fof(f391,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f389,f285,f78,f73,f69])).

fof(f69,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,
    ( spl4_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f285,plain,
    ( spl4_25
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f389,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(superposition,[],[f277,f383])).

fof(f383,plain,
    ( ! [X2] : sK1 = k3_xboole_0(sK1,X2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,
    ( ! [X2] :
        ( sK1 = k3_xboole_0(sK1,X2)
        | sK1 = k3_xboole_0(sK1,X2) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(resolution,[],[f380,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f380,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | sK1 = k3_xboole_0(sK1,X0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(duplicate_literal_removal,[],[f378])).

fof(f378,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | sK1 = k3_xboole_0(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(resolution,[],[f338,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f338,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK1,X0),sK1)
        | r1_tarski(sK1,X0)
        | sK1 = k3_xboole_0(sK1,X0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(resolution,[],[f336,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f122,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f48,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(global_subsumption,[],[f37,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f42,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK1,X0),sK0)
        | sK1 = k3_xboole_0(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(resolution,[],[f320,f49])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK1,X0),sK1)
        | ~ r2_hidden(sK2(sK1,X0),sK0)
        | sK1 = k3_xboole_0(sK1,X0) )
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(resolution,[],[f319,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f319,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,X2),k5_xboole_0(sK0,sK1))
        | sK1 = k3_xboole_0(sK1,X2) )
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(resolution,[],[f305,f46])).

fof(f305,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,X1)
        | r2_hidden(sK2(sK1,X1),k5_xboole_0(sK0,sK1)) )
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(resolution,[],[f294,f49])).

fof(f294,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,k5_xboole_0(sK0,sK1)) )
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(superposition,[],[f181,f286])).

fof(f286,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f181,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f277,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f275,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f275,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f252,f46])).

fof(f252,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[],[f248,f49])).

fof(f248,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f169,f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f58,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f56,f39])).

fof(f287,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f283,f192,f78,f285])).

fof(f192,plain,
    ( spl4_17
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f283,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f281,f193])).

fof(f193,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f281,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f61,f79])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f258,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f67,f252])).

fof(f67,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f197,plain,
    ( spl4_17
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f190,f176,f192])).

fof(f176,plain,
    ( spl4_15
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f190,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_15 ),
    inference(superposition,[],[f40,f177])).

fof(f177,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl4_15
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f123,f78,f176])).

fof(f123,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f104,f79])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f46,f88])).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f76,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f60,f69,f73])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f35,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f64,f69,f66])).

fof(f64,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:32:31 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.53  % (4681)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (4679)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (4689)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (4692)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (4689)Refutation not found, incomplete strategy% (4689)------------------------------
% 0.22/0.53  % (4689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4704)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (4696)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (4689)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4689)Memory used [KB]: 10618
% 0.22/0.53  % (4689)Time elapsed: 0.111 s
% 0.22/0.53  % (4689)------------------------------
% 0.22/0.53  % (4689)------------------------------
% 0.22/0.53  % (4682)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (4680)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (4684)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (4691)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (4694)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (4699)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (4698)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (4685)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (4700)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (4708)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (4690)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (4683)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (4686)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (4688)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (4687)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (4702)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (4697)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (4687)Refutation not found, incomplete strategy% (4687)------------------------------
% 0.22/0.56  % (4687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4687)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4687)Memory used [KB]: 10746
% 0.22/0.56  % (4687)Time elapsed: 0.139 s
% 0.22/0.56  % (4687)------------------------------
% 0.22/0.56  % (4687)------------------------------
% 0.22/0.56  % (4695)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (4705)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (4707)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (4703)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (4698)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (4706)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.59  % (4701)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.59  fof(f392,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(avatar_sat_refutation,[],[f71,f76,f80,f178,f197,f258,f287,f391])).
% 1.62/0.59  fof(f391,plain,(
% 1.62/0.59    spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_25),
% 1.62/0.59    inference(avatar_split_clause,[],[f389,f285,f78,f73,f69])).
% 1.62/0.59  fof(f69,plain,(
% 1.62/0.59    spl4_2 <=> k1_xboole_0 = sK1),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.62/0.59  fof(f73,plain,(
% 1.62/0.59    spl4_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.62/0.59  fof(f78,plain,(
% 1.62/0.59    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.62/0.59  fof(f285,plain,(
% 1.62/0.59    spl4_25 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.62/0.59  fof(f389,plain,(
% 1.62/0.59    k1_xboole_0 = sK1 | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 1.62/0.59    inference(superposition,[],[f277,f383])).
% 1.62/0.59  fof(f383,plain,(
% 1.62/0.59    ( ! [X2] : (sK1 = k3_xboole_0(sK1,X2)) ) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f382])).
% 1.62/0.59  fof(f382,plain,(
% 1.62/0.59    ( ! [X2] : (sK1 = k3_xboole_0(sK1,X2) | sK1 = k3_xboole_0(sK1,X2)) ) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f380,f46])).
% 1.62/0.59  fof(f46,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f16])).
% 1.62/0.59  fof(f16,plain,(
% 1.62/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f5])).
% 1.62/0.59  fof(f5,axiom,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.62/0.59  fof(f380,plain,(
% 1.62/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | sK1 = k3_xboole_0(sK1,X0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f378])).
% 1.62/0.59  fof(f378,plain,(
% 1.62/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | sK1 = k3_xboole_0(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f338,f49])).
% 1.62/0.59  fof(f49,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.59    inference(rectify,[],[f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.59    inference(nnf_transformation,[],[f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.59  fof(f338,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(sK2(sK1,X0),sK1) | r1_tarski(sK1,X0) | sK1 = k3_xboole_0(sK1,X0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f336,f149])).
% 1.62/0.59  fof(f149,plain,(
% 1.62/0.59    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl4_4),
% 1.62/0.59    inference(resolution,[],[f122,f79])).
% 1.62/0.59  fof(f79,plain,(
% 1.62/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 1.62/0.59    inference(avatar_component_clause,[],[f78])).
% 1.62/0.59  fof(f122,plain,(
% 1.62/0.59    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | r2_hidden(X3,X5) | ~r2_hidden(X3,X4)) )),
% 1.62/0.59    inference(resolution,[],[f48,f88])).
% 1.62/0.59  fof(f88,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.62/0.59    inference(global_subsumption,[],[f37,f87])).
% 1.62/0.59  fof(f87,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(resolution,[],[f42,f63])).
% 1.62/0.59  fof(f63,plain,(
% 1.62/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.62/0.59    inference(equality_resolution,[],[f51])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f32])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.62/0.59    inference(rectify,[],[f29])).
% 1.62/0.59  fof(f29,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.62/0.59  fof(f42,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.62/0.59    inference(nnf_transformation,[],[f15])).
% 1.62/0.59  fof(f15,plain,(
% 1.62/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,axiom,(
% 1.62/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.62/0.59  fof(f48,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f336,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(sK2(sK1,X0),sK0) | sK1 = k3_xboole_0(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl4_3 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f320,f49])).
% 1.62/0.59  fof(f320,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(sK2(sK1,X0),sK1) | ~r2_hidden(sK2(sK1,X0),sK0) | sK1 = k3_xboole_0(sK1,X0)) ) | (~spl4_3 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f319,f56])).
% 1.62/0.59  fof(f56,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f33])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.62/0.59    inference(nnf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.62/0.59    inference(ennf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.62/0.59  fof(f319,plain,(
% 1.62/0.59    ( ! [X2] : (r2_hidden(sK2(sK1,X2),k5_xboole_0(sK0,sK1)) | sK1 = k3_xboole_0(sK1,X2)) ) | (~spl4_3 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f305,f46])).
% 1.62/0.59  fof(f305,plain,(
% 1.62/0.59    ( ! [X1] : (r1_tarski(sK1,X1) | r2_hidden(sK2(sK1,X1),k5_xboole_0(sK0,sK1))) ) | (~spl4_3 | ~spl4_25)),
% 1.62/0.59    inference(resolution,[],[f294,f49])).
% 1.62/0.59  fof(f294,plain,(
% 1.62/0.59    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,k5_xboole_0(sK0,sK1))) ) | (~spl4_3 | ~spl4_25)),
% 1.62/0.59    inference(superposition,[],[f181,f286])).
% 1.62/0.59  fof(f286,plain,(
% 1.62/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl4_25),
% 1.62/0.59    inference(avatar_component_clause,[],[f285])).
% 1.62/0.59  fof(f181,plain,(
% 1.62/0.59    ( ! [X0] : (r2_hidden(X0,k3_subset_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl4_3),
% 1.62/0.59    inference(resolution,[],[f74,f48])).
% 1.62/0.59  fof(f74,plain,(
% 1.62/0.59    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl4_3),
% 1.62/0.59    inference(avatar_component_clause,[],[f73])).
% 1.62/0.59  fof(f277,plain,(
% 1.62/0.59    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f275,f40])).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.62/0.59  fof(f275,plain,(
% 1.62/0.59    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 1.62/0.59    inference(resolution,[],[f252,f46])).
% 1.62/0.59  fof(f252,plain,(
% 1.62/0.59    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.62/0.59    inference(resolution,[],[f248,f49])).
% 1.62/0.59  fof(f248,plain,(
% 1.62/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(global_subsumption,[],[f169,f245])).
% 1.62/0.59  fof(f245,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f244])).
% 1.62/0.59  fof(f244,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f58,f39])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f33])).
% 1.62/0.59  fof(f169,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f168])).
% 1.62/0.59  fof(f168,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f56,f39])).
% 1.62/0.59  fof(f287,plain,(
% 1.62/0.59    spl4_25 | ~spl4_4 | ~spl4_17),
% 1.62/0.59    inference(avatar_split_clause,[],[f283,f192,f78,f285])).
% 1.62/0.59  fof(f192,plain,(
% 1.62/0.59    spl4_17 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.62/0.59  fof(f283,plain,(
% 1.62/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | (~spl4_4 | ~spl4_17)),
% 1.62/0.59    inference(forward_demodulation,[],[f281,f193])).
% 1.62/0.59  fof(f193,plain,(
% 1.62/0.59    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_17),
% 1.62/0.59    inference(avatar_component_clause,[],[f192])).
% 1.62/0.59  fof(f281,plain,(
% 1.62/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl4_4),
% 1.62/0.59    inference(resolution,[],[f61,f79])).
% 1.62/0.59  fof(f61,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f47,f41])).
% 1.62/0.59  fof(f41,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f17])).
% 1.62/0.59  fof(f17,plain,(
% 1.62/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,axiom,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.62/0.59  fof(f258,plain,(
% 1.62/0.59    spl4_1),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f257])).
% 1.62/0.59  fof(f257,plain,(
% 1.62/0.59    $false | spl4_1),
% 1.62/0.59    inference(subsumption_resolution,[],[f67,f252])).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl4_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f66])).
% 1.62/0.59  fof(f66,plain,(
% 1.62/0.59    spl4_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.62/0.59  fof(f197,plain,(
% 1.62/0.59    spl4_17 | ~spl4_15),
% 1.62/0.59    inference(avatar_split_clause,[],[f190,f176,f192])).
% 1.62/0.59  fof(f176,plain,(
% 1.62/0.59    spl4_15 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.62/0.59  fof(f190,plain,(
% 1.62/0.59    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_15),
% 1.62/0.59    inference(superposition,[],[f40,f177])).
% 1.62/0.59  fof(f177,plain,(
% 1.62/0.59    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_15),
% 1.62/0.59    inference(avatar_component_clause,[],[f176])).
% 1.62/0.59  fof(f178,plain,(
% 1.62/0.59    spl4_15 | ~spl4_4),
% 1.62/0.59    inference(avatar_split_clause,[],[f123,f78,f176])).
% 1.62/0.59  fof(f123,plain,(
% 1.62/0.59    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_4),
% 1.62/0.59    inference(resolution,[],[f104,f79])).
% 1.62/0.59  fof(f104,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0) )),
% 1.62/0.59    inference(resolution,[],[f46,f88])).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    spl4_4),
% 1.62/0.59    inference(avatar_split_clause,[],[f34,f78])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    inference(cnf_transformation,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(flattening,[],[f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(nnf_transformation,[],[f14])).
% 1.62/0.59  fof(f14,plain,(
% 1.62/0.59    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.62/0.59    inference(negated_conjecture,[],[f12])).
% 1.62/0.59  fof(f12,conjecture,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.62/0.59  fof(f76,plain,(
% 1.62/0.59    spl4_3 | spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f60,f69,f73])).
% 1.62/0.59  fof(f60,plain,(
% 1.62/0.59    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.62/0.59    inference(definition_unfolding,[],[f35,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f23])).
% 1.62/0.59  fof(f71,plain,(
% 1.62/0.59    ~spl4_1 | ~spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f64,f69,f66])).
% 1.62/0.59  fof(f64,plain,(
% 1.62/0.59    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(inner_rewriting,[],[f59])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.62/0.59    inference(definition_unfolding,[],[f36,f38])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f23])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (4698)------------------------------
% 1.62/0.59  % (4698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (4698)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (4698)Memory used [KB]: 10874
% 1.62/0.59  % (4698)Time elapsed: 0.156 s
% 1.62/0.59  % (4698)------------------------------
% 1.62/0.59  % (4698)------------------------------
% 1.62/0.59  % (4678)Success in time 0.223 s
%------------------------------------------------------------------------------
