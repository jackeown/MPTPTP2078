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
% DateTime   : Thu Dec  3 12:56:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 143 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  260 ( 575 expanded)
%              Number of equality atoms :   34 (  82 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f66,f71,f86,f97,f101,f104])).

fof(f104,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f92,f84,f99,f94])).

fof(f94,plain,
    ( spl7_6
  <=> r2_hidden(sK6(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f99,plain,
    ( spl7_7
  <=> r2_hidden(sK5(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f84,plain,
    ( spl7_5
  <=> sK0 = k4_tarski(sK5(sK0),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( ~ r2_hidden(sK5(sK0),sK1)
    | ~ r2_hidden(sK6(sK0),sK2)
    | ~ spl7_5 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK5(sK0),sK1)
    | ~ r2_hidden(sK6(sK0),sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f31,f85])).

fof(f85,plain,
    ( sK0 = k4_tarski(sK5(sK0),sK6(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f31,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1)
        | k4_tarski(X4,X5) != sK0 )
    & r2_hidden(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1)
          | k4_tarski(X4,X5) != sK0 )
      & r2_hidden(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f101,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f89,f84,f69,f51,f99])).

fof(f51,plain,
    ( spl7_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f69,plain,
    ( spl7_4
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f89,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK5(sK0),sK1)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f74,f85])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X0,sK1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f73,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f73,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X3,sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f60,f70])).

fof(f70,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f48,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

% (10896)Refutation not found, incomplete strategy% (10896)------------------------------
% (10896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10896)Termination reason: Refutation not found, incomplete strategy

% (10896)Memory used [KB]: 10618
% (10896)Time elapsed: 0.061 s
% (10896)------------------------------
% (10896)------------------------------
% (10909)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (10904)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (10910)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f97,plain,
    ( spl7_6
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f87,f84,f69,f51,f94])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK6(sK0),sK2)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f75,f85])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK3)
        | r2_hidden(X0,sK2) )
    | ~ spl7_4 ),
    inference(resolution,[],[f45,f73])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( spl7_5
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f82,f69,f51,f84])).

fof(f82,plain,
    ( sK0 = k4_tarski(sK5(sK0),sK6(sK0))
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | k4_tarski(sK5(X0),sK6(X0)) = X0 )
    | ~ spl7_4 ),
    inference(resolution,[],[f43,f73])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f71,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f67,f64,f69])).

fof(f64,plain,
    ( spl7_3
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f67,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl7_3 ),
    inference(resolution,[],[f65,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f65,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f62,f55,f64])).

fof(f55,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f62,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_2 ),
    inference(resolution,[],[f59,f56])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f57,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:36:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (10896)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (10901)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (10901)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f53,f57,f66,f71,f86,f97,f101,f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ~spl7_6 | ~spl7_7 | ~spl7_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f92,f84,f99,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl7_6 <=> r2_hidden(sK6(sK0),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl7_7 <=> r2_hidden(sK5(sK0),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl7_5 <=> sK0 = k4_tarski(sK5(sK0),sK6(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ~r2_hidden(sK5(sK0),sK1) | ~r2_hidden(sK6(sK0),sK2) | ~spl7_5),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    sK0 != sK0 | ~r2_hidden(sK5(sK0),sK1) | ~r2_hidden(sK6(sK0),sK2) | ~spl7_5),
% 0.22/0.48    inference(superposition,[],[f31,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) | ~spl7_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X4,X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    spl7_7 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f89,f84,f69,f51,f99])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl7_1 <=> r2_hidden(sK0,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl7_4 <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK3) | r2_hidden(sK5(sK0),sK1) | (~spl7_4 | ~spl7_5)),
% 0.22/0.48    inference(superposition,[],[f74,f85])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK1)) ) | ~spl7_4),
% 0.22/0.48    inference(resolution,[],[f73,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.48    inference(nnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X3] : (r2_hidden(X3,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X3,sK3)) ) | ~spl7_4),
% 0.22/0.48    inference(resolution,[],[f60,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl7_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f69])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(superposition,[],[f48,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(rectify,[],[f21])).
% 0.22/0.48  % (10896)Refutation not found, incomplete strategy% (10896)------------------------------
% 0.22/0.48  % (10896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10896)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (10896)Memory used [KB]: 10618
% 0.22/0.48  % (10896)Time elapsed: 0.061 s
% 0.22/0.48  % (10896)------------------------------
% 0.22/0.48  % (10896)------------------------------
% 0.22/0.48  % (10909)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (10904)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (10910)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl7_6 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f87,f84,f69,f51,f94])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~r2_hidden(sK0,sK3) | r2_hidden(sK6(sK0),sK2) | (~spl7_4 | ~spl7_5)),
% 0.22/0.49    inference(superposition,[],[f75,f85])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK3) | r2_hidden(X0,sK2)) ) | ~spl7_4),
% 0.22/0.49    inference(resolution,[],[f45,f73])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl7_5 | ~spl7_1 | ~spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f82,f69,f51,f84])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) | (~spl7_1 | ~spl7_4)),
% 0.22/0.49    inference(resolution,[],[f81,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    r2_hidden(sK0,sK3) | ~spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f51])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK3) | k4_tarski(sK5(X0),sK6(X0)) = X0) ) | ~spl7_4),
% 0.22/0.49    inference(resolution,[],[f43,f73])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK5(X0),sK6(X0)) = X0)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl7_4 | ~spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f67,f64,f69])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl7_3 <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl7_3),
% 0.22/0.49    inference(resolution,[],[f65,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.22/0.49    inference(superposition,[],[f36,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl7_3 | ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f62,f55,f64])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_2),
% 0.22/0.49    inference(resolution,[],[f59,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(resolution,[],[f35,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f55])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f51])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    r2_hidden(sK0,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10901)------------------------------
% 0.22/0.49  % (10901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10901)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10901)Memory used [KB]: 10618
% 0.22/0.49  % (10901)Time elapsed: 0.064 s
% 0.22/0.49  % (10901)------------------------------
% 0.22/0.49  % (10901)------------------------------
% 0.22/0.49  % (10894)Success in time 0.127 s
%------------------------------------------------------------------------------
