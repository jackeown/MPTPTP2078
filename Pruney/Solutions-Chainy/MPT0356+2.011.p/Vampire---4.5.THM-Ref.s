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
% DateTime   : Thu Dec  3 12:44:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 136 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  228 ( 497 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (3006)Refutation not found, incomplete strategy% (3006)------------------------------
% (3006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f270,f274,f314])).

fof(f314,plain,(
    ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f312,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
        & r1_tarski(sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f311,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f311,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_15 ),
    inference(superposition,[],[f269,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f269,plain,
    ( r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl4_15
  <=> r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f274,plain,
    ( ~ spl4_9
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl4_9
    | spl4_14 ),
    inference(subsumption_resolution,[],[f271,f218])).

fof(f218,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f217,f163])).

fof(f163,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_9
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f217,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_9 ),
    inference(superposition,[],[f216,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k3_subset_1(X0,k1_xboole_0) = X0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f61,f31])).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f61,plain,(
    ! [X0] :
      ( k3_subset_1(X0,k1_xboole_0) = X0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

% (3000)Refutation not found, incomplete strategy% (3000)------------------------------
% (3000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3000)Termination reason: Refutation not found, incomplete strategy

% (3000)Memory used [KB]: 10746
% (3000)Time elapsed: 0.127 s
% (3000)------------------------------
% (3000)------------------------------
fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f48,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f216,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k1_xboole_0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f215,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f215,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k1_xboole_0))
    | ~ spl4_9 ),
    inference(resolution,[],[f143,f163])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r1_tarski(X0,sK2)
      | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f124,f31])).

fof(f124,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,sK2)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f87,f36])).

fof(f87,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X1))
      | ~ r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f271,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | spl4_14 ),
    inference(resolution,[],[f265,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f265,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f263])).

% (3012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f263,plain,
    ( spl4_14
  <=> r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f270,plain,
    ( ~ spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f260,f267,f263])).

fof(f260,plain,
    ( r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1))
    | ~ r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f246,f29])).

fof(f29,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f246,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f89,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X4))
      | r1_tarski(k3_subset_1(X4,X3),k3_subset_1(X4,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X3,k1_zfmisc_1(X4)) ) ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k3_subset_1(X4,X3),k3_subset_1(X4,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
      | ~ r2_hidden(X3,k1_zfmisc_1(X4))
      | v1_xboole_0(k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f41,f36])).

fof(f173,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f170,f32])).

fof(f170,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl4_9 ),
    inference(resolution,[],[f164,f49])).

fof(f164,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3008)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (3010)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (3001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (3008)Refutation not found, incomplete strategy% (3008)------------------------------
% 0.20/0.51  % (3008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3008)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3008)Memory used [KB]: 10618
% 0.20/0.51  % (3008)Time elapsed: 0.105 s
% 0.20/0.51  % (3008)------------------------------
% 0.20/0.51  % (3008)------------------------------
% 0.20/0.51  % (3016)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (3001)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (3022)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.52  % (3006)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.53  % (3013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.53  % (3000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (3026)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  % (2998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.53  % (3006)Refutation not found, incomplete strategy% (3006)------------------------------
% 1.24/0.53  % (3006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  fof(f315,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(avatar_sat_refutation,[],[f173,f270,f274,f314])).
% 1.24/0.53  fof(f314,plain,(
% 1.24/0.53    ~spl4_15),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f313])).
% 1.24/0.53  fof(f313,plain,(
% 1.24/0.53    $false | ~spl4_15),
% 1.24/0.53    inference(subsumption_resolution,[],[f312,f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.24/0.53    inference(cnf_transformation,[],[f20])).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18])).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f19,plain,(
% 1.24/0.53    ? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f13,plain,(
% 1.24/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(flattening,[],[f12])).
% 1.24/0.53  fof(f12,plain,(
% 1.24/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.24/0.53    inference(negated_conjecture,[],[f10])).
% 1.24/0.53  fof(f10,conjecture,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.24/0.53  fof(f312,plain,(
% 1.24/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_15),
% 1.24/0.53    inference(subsumption_resolution,[],[f311,f30])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.24/0.53    inference(cnf_transformation,[],[f20])).
% 1.24/0.53  fof(f311,plain,(
% 1.24/0.53    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_15),
% 1.24/0.53    inference(superposition,[],[f269,f40])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f16])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.24/0.53  fof(f269,plain,(
% 1.24/0.53    r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1)) | ~spl4_15),
% 1.24/0.53    inference(avatar_component_clause,[],[f267])).
% 1.24/0.53  fof(f267,plain,(
% 1.24/0.53    spl4_15 <=> r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.24/0.53  fof(f274,plain,(
% 1.24/0.53    ~spl4_9 | spl4_14),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f273])).
% 1.24/0.53  fof(f273,plain,(
% 1.24/0.53    $false | (~spl4_9 | spl4_14)),
% 1.24/0.53    inference(subsumption_resolution,[],[f271,f218])).
% 1.24/0.53  fof(f218,plain,(
% 1.24/0.53    r1_tarski(k3_subset_1(sK0,sK2),sK0) | ~spl4_9),
% 1.24/0.53    inference(subsumption_resolution,[],[f217,f163])).
% 1.24/0.53  fof(f163,plain,(
% 1.24/0.53    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_9),
% 1.24/0.53    inference(avatar_component_clause,[],[f162])).
% 1.24/0.53  fof(f162,plain,(
% 1.24/0.53    spl4_9 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.24/0.53  fof(f217,plain,(
% 1.24/0.53    r1_tarski(k3_subset_1(sK0,sK2),sK0) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_9),
% 1.24/0.53    inference(superposition,[],[f216,f62])).
% 1.24/0.53  fof(f62,plain,(
% 1.24/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0 | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(subsumption_resolution,[],[f61,f31])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.24/0.53  fof(f61,plain,(
% 1.24/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0 | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(resolution,[],[f59,f36])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f21])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.24/0.53    inference(nnf_transformation,[],[f14])).
% 1.24/0.53  fof(f14,plain,(
% 1.24/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.24/0.53  % (3000)Refutation not found, incomplete strategy% (3000)------------------------------
% 1.24/0.53  % (3000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (3000)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (3000)Memory used [KB]: 10746
% 1.24/0.53  % (3000)Time elapsed: 0.127 s
% 1.24/0.53  % (3000)------------------------------
% 1.24/0.53  % (3000)------------------------------
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.24/0.53    inference(superposition,[],[f48,f47])).
% 1.24/0.53  fof(f47,plain,(
% 1.24/0.53    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.24/0.53    inference(definition_unfolding,[],[f33,f34])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.24/0.53  fof(f48,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(definition_unfolding,[],[f39,f34])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f15])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,axiom,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.24/0.53  fof(f216,plain,(
% 1.24/0.53    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k1_xboole_0)) | ~spl4_9),
% 1.24/0.53    inference(subsumption_resolution,[],[f215,f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.24/0.53  fof(f215,plain,(
% 1.24/0.53    ~r1_tarski(k1_xboole_0,sK2) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k1_xboole_0)) | ~spl4_9),
% 1.24/0.53    inference(resolution,[],[f143,f163])).
% 1.24/0.53  fof(f143,plain,(
% 1.24/0.53    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r1_tarski(X0,sK2) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0))) )),
% 1.24/0.53    inference(subsumption_resolution,[],[f124,f31])).
% 1.24/0.53  fof(f124,plain,(
% 1.24/0.53    ( ! [X0] : (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) | ~r1_tarski(X0,sK2) | ~r2_hidden(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 1.24/0.53    inference(resolution,[],[f87,f36])).
% 1.24/0.53  fof(f87,plain,(
% 1.24/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X1)) | ~r1_tarski(X1,sK2)) )),
% 1.24/0.53    inference(resolution,[],[f41,f28])).
% 1.24/0.53  fof(f41,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f22])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(nnf_transformation,[],[f17])).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f9])).
% 1.24/0.53  fof(f9,axiom,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.24/0.53  fof(f271,plain,(
% 1.24/0.53    ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl4_14),
% 1.24/0.53    inference(resolution,[],[f265,f49])).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.24/0.53    inference(equality_resolution,[],[f44])).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.53    inference(rectify,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.53    inference(nnf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.24/0.53  fof(f265,plain,(
% 1.24/0.53    ~r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl4_14),
% 1.24/0.53    inference(avatar_component_clause,[],[f263])).
% 1.24/0.53  % (3012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.53  fof(f263,plain,(
% 1.24/0.53    spl4_14 <=> r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.24/0.53  fof(f270,plain,(
% 1.24/0.53    ~spl4_14 | spl4_15),
% 1.24/0.53    inference(avatar_split_clause,[],[f260,f267,f263])).
% 1.24/0.53  fof(f260,plain,(
% 1.24/0.53    r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1)) | ~r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.24/0.53    inference(resolution,[],[f246,f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.24/0.53    inference(cnf_transformation,[],[f20])).
% 1.24/0.53  fof(f246,plain,(
% 1.24/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK1)) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 1.24/0.53    inference(resolution,[],[f89,f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.24/0.53    inference(cnf_transformation,[],[f20])).
% 1.24/0.53  fof(f89,plain,(
% 1.24/0.53    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X4)) | r1_tarski(k3_subset_1(X4,X3),k3_subset_1(X4,X2)) | ~r1_tarski(X2,X3) | ~r2_hidden(X3,k1_zfmisc_1(X4))) )),
% 1.24/0.53    inference(subsumption_resolution,[],[f88,f31])).
% 1.24/0.53  fof(f88,plain,(
% 1.24/0.53    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k3_subset_1(X4,X3),k3_subset_1(X4,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X4)) | ~r2_hidden(X3,k1_zfmisc_1(X4)) | v1_xboole_0(k1_zfmisc_1(X4))) )),
% 1.24/0.53    inference(resolution,[],[f41,f36])).
% 1.24/0.53  fof(f173,plain,(
% 1.24/0.53    spl4_9),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f172])).
% 1.24/0.53  fof(f172,plain,(
% 1.24/0.53    $false | spl4_9),
% 1.24/0.53    inference(subsumption_resolution,[],[f170,f32])).
% 1.24/0.53  fof(f170,plain,(
% 1.24/0.53    ~r1_tarski(k1_xboole_0,sK0) | spl4_9),
% 1.24/0.53    inference(resolution,[],[f164,f49])).
% 1.24/0.53  fof(f164,plain,(
% 1.24/0.53    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | spl4_9),
% 1.24/0.53    inference(avatar_component_clause,[],[f162])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (3001)------------------------------
% 1.24/0.53  % (3001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (3001)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (3001)Memory used [KB]: 10874
% 1.24/0.53  % (3001)Time elapsed: 0.107 s
% 1.24/0.53  % (3001)------------------------------
% 1.24/0.53  % (3001)------------------------------
% 1.24/0.54  % (3018)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.54  % (2996)Success in time 0.174 s
%------------------------------------------------------------------------------
