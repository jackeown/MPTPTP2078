%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:26 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 172 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 ( 650 expanded)
%              Number of equality atoms :   51 ( 127 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f757,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f88,f206,f756])).

fof(f756,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f754,f86])).

fof(f86,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f754,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f753])).

fof(f753,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f725,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f725,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(k2_relat_1(sK1),X4),sK0)
        | r1_xboole_0(k2_relat_1(sK1),X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f720,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f720,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f712,f96])).

fof(f96,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f50,f46])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f712,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK1,X6))
        | ~ r2_hidden(X5,sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f711,f46])).

fof(f711,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,sK0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X5,k9_relat_1(sK1,X6)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f698,f93])).

fof(f93,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f698,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK3(X5,X6,sK1),k1_xboole_0)
        | ~ r2_hidden(X5,sK0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X5,k9_relat_1(sK1,X6)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f307,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f307,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X2,X3),k10_relat_1(X3,X1))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,k9_relat_1(X3,X2)) ) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK3(X0,X2,X3),k10_relat_1(X3,X1))
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,k9_relat_1(X3,X2))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f283,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

% (7199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f283,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f71,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f206,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f204,f82])).

fof(f82,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f204,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f203,f183])).

fof(f183,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f167,f46])).

fof(f167,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k1_xboole_0 = k10_relat_1(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f161,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f136,f77])).

% (7194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k1_xboole_0 = X1
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f72,f77])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (7207)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f161,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k10_relat_1(X0,k1_xboole_0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f158,f52])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X1,k1_xboole_0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f70,f93])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f203,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f176,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f76,f85])).

fof(f85,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f60,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f176,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))) ),
    inference(resolution,[],[f74,f46])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f88,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f47,f84,f80])).

fof(f47,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f84,f80])).

fof(f48,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : run_vampire %s %d
% 0.09/0.27  % Computer   : n020.cluster.edu
% 0.09/0.27  % Model      : x86_64 x86_64
% 0.09/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.27  % Memory     : 8042.1875MB
% 0.09/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.27  % CPULimit   : 60
% 0.09/0.27  % WCLimit    : 600
% 0.09/0.27  % DateTime   : Tue Dec  1 13:23:37 EST 2020
% 0.12/0.27  % CPUTime    : 
% 0.13/0.39  % (7200)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.13/0.40  % (7192)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.13/0.40  % (7183)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.13/0.40  % (7181)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.13/0.40  % (7180)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.13/0.41  % (7182)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.13/0.41  % (7184)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.13/0.42  % (7178)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.13/0.43  % (7206)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.13/0.43  % (7205)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.13/0.43  % (7179)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.13/0.43  % (7201)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.13/0.44  % (7202)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.13/0.44  % (7185)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.13/0.44  % (7196)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.13/0.44  % (7197)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.13/0.44  % (7198)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.13/0.45  % (7188)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.13/0.45  % (7188)Refutation not found, incomplete strategy% (7188)------------------------------
% 0.13/0.45  % (7188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.45  % (7188)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.45  
% 0.13/0.45  % (7188)Memory used [KB]: 10746
% 0.13/0.45  % (7188)Time elapsed: 0.130 s
% 0.13/0.45  % (7188)------------------------------
% 0.13/0.45  % (7188)------------------------------
% 0.13/0.45  % (7191)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.13/0.45  % (7190)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.13/0.45  % (7189)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.13/0.46  % (7206)Refutation not found, incomplete strategy% (7206)------------------------------
% 0.13/0.46  % (7206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.46  % (7206)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.46  
% 0.13/0.46  % (7206)Memory used [KB]: 10746
% 0.13/0.46  % (7206)Time elapsed: 0.137 s
% 0.13/0.46  % (7206)------------------------------
% 0.13/0.46  % (7206)------------------------------
% 0.13/0.46  % (7204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.13/0.46  % (7195)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.13/0.46  % (7184)Refutation found. Thanks to Tanya!
% 0.13/0.46  % SZS status Theorem for theBenchmark
% 0.13/0.46  % SZS output start Proof for theBenchmark
% 0.13/0.46  fof(f757,plain,(
% 0.13/0.46    $false),
% 0.13/0.46    inference(avatar_sat_refutation,[],[f87,f88,f206,f756])).
% 0.13/0.46  fof(f756,plain,(
% 0.13/0.46    ~spl5_1 | spl5_2),
% 0.13/0.46    inference(avatar_contradiction_clause,[],[f755])).
% 0.13/0.46  fof(f755,plain,(
% 0.13/0.46    $false | (~spl5_1 | spl5_2)),
% 0.13/0.46    inference(subsumption_resolution,[],[f754,f86])).
% 0.13/0.46  fof(f86,plain,(
% 0.13/0.46    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl5_2),
% 0.13/0.46    inference(avatar_component_clause,[],[f84])).
% 0.13/0.46  fof(f84,plain,(
% 0.13/0.46    spl5_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.13/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.13/0.46  fof(f754,plain,(
% 0.13/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl5_1),
% 0.13/0.46    inference(duplicate_literal_removal,[],[f753])).
% 0.13/0.46  fof(f753,plain,(
% 0.13/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl5_1),
% 0.13/0.46    inference(resolution,[],[f725,f53])).
% 0.13/0.46  fof(f53,plain,(
% 0.13/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f34])).
% 0.13/0.46  fof(f34,plain,(
% 0.13/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.13/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f33])).
% 0.13/0.46  fof(f33,plain,(
% 0.13/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.13/0.46    introduced(choice_axiom,[])).
% 0.13/0.46  fof(f19,plain,(
% 0.13/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.13/0.46    inference(ennf_transformation,[],[f16])).
% 0.13/0.46  fof(f16,plain,(
% 0.13/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.13/0.46    inference(rectify,[],[f3])).
% 0.13/0.46  fof(f3,axiom,(
% 0.13/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.13/0.46  fof(f725,plain,(
% 0.13/0.46    ( ! [X4] : (~r2_hidden(sK2(k2_relat_1(sK1),X4),sK0) | r1_xboole_0(k2_relat_1(sK1),X4)) ) | ~spl5_1),
% 0.13/0.46    inference(resolution,[],[f720,f52])).
% 0.13/0.46  fof(f52,plain,(
% 0.13/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f34])).
% 0.13/0.46  fof(f720,plain,(
% 0.13/0.46    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_1),
% 0.13/0.46    inference(superposition,[],[f712,f96])).
% 0.13/0.46  fof(f96,plain,(
% 0.13/0.46    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.13/0.46    inference(resolution,[],[f50,f46])).
% 0.13/0.46  fof(f46,plain,(
% 0.13/0.46    v1_relat_1(sK1)),
% 0.13/0.46    inference(cnf_transformation,[],[f32])).
% 0.13/0.46  fof(f32,plain,(
% 0.13/0.46    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.13/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 0.13/0.46  fof(f31,plain,(
% 0.13/0.46    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.13/0.46    introduced(choice_axiom,[])).
% 0.13/0.46  fof(f30,plain,(
% 0.13/0.46    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.13/0.46    inference(flattening,[],[f29])).
% 0.13/0.46  fof(f29,plain,(
% 0.13/0.46    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.13/0.46    inference(nnf_transformation,[],[f17])).
% 0.13/0.46  fof(f17,plain,(
% 0.13/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.13/0.46    inference(ennf_transformation,[],[f15])).
% 0.13/0.46  fof(f15,negated_conjecture,(
% 0.13/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.13/0.46    inference(negated_conjecture,[],[f14])).
% 0.13/0.46  fof(f14,conjecture,(
% 0.13/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.13/0.46  fof(f50,plain,(
% 0.13/0.46    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f18])).
% 0.13/0.46  fof(f18,plain,(
% 0.13/0.46    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.46    inference(ennf_transformation,[],[f10])).
% 0.13/0.46  fof(f10,axiom,(
% 0.13/0.46    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.13/0.46  fof(f712,plain,(
% 0.13/0.46    ( ! [X6,X5] : (~r2_hidden(X5,k9_relat_1(sK1,X6)) | ~r2_hidden(X5,sK0)) ) | ~spl5_1),
% 0.13/0.46    inference(subsumption_resolution,[],[f711,f46])).
% 0.13/0.46  fof(f711,plain,(
% 0.13/0.46    ( ! [X6,X5] : (~r2_hidden(X5,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X5,k9_relat_1(sK1,X6))) ) | ~spl5_1),
% 0.13/0.46    inference(subsumption_resolution,[],[f698,f93])).
% 0.13/0.46  fof(f93,plain,(
% 0.13/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.13/0.46    inference(resolution,[],[f73,f49])).
% 0.13/0.46  fof(f49,plain,(
% 0.13/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f5])).
% 0.13/0.46  fof(f5,axiom,(
% 0.13/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.13/0.46  fof(f73,plain,(
% 0.13/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f28])).
% 0.13/0.46  fof(f28,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.13/0.46    inference(ennf_transformation,[],[f7])).
% 0.13/0.46  fof(f7,axiom,(
% 0.13/0.46    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.13/0.46  fof(f698,plain,(
% 0.13/0.46    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,sK1),k1_xboole_0) | ~r2_hidden(X5,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X5,k9_relat_1(sK1,X6))) ) | ~spl5_1),
% 0.13/0.46    inference(superposition,[],[f307,f81])).
% 0.13/0.46  fof(f81,plain,(
% 0.13/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl5_1),
% 0.13/0.46    inference(avatar_component_clause,[],[f80])).
% 0.13/0.46  fof(f80,plain,(
% 0.13/0.46    spl5_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.13/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.13/0.46  fof(f307,plain,(
% 0.13/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X0,X2,X3),k10_relat_1(X3,X1)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X3) | ~r2_hidden(X0,k9_relat_1(X3,X2))) )),
% 0.13/0.46    inference(duplicate_literal_removal,[],[f304])).
% 0.13/0.46  fof(f304,plain,(
% 0.13/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK3(X0,X2,X3),k10_relat_1(X3,X1)) | ~v1_relat_1(X3) | ~r2_hidden(X0,k9_relat_1(X3,X2)) | ~v1_relat_1(X3)) )),
% 0.13/0.46    inference(resolution,[],[f283,f65])).
% 0.13/0.46  fof(f65,plain,(
% 0.13/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f41])).
% 0.13/0.46  fof(f41,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.13/0.46  fof(f40,plain,(
% 0.13/0.46    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.13/0.46    introduced(choice_axiom,[])).
% 0.13/0.46  fof(f39,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(rectify,[],[f38])).
% 0.13/0.46  % (7199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.13/0.46  fof(f38,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(nnf_transformation,[],[f24])).
% 0.13/0.46  fof(f24,plain,(
% 0.13/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(ennf_transformation,[],[f9])).
% 0.13/0.46  fof(f9,axiom,(
% 0.13/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.13/0.46  fof(f283,plain,(
% 0.13/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.13/0.46    inference(subsumption_resolution,[],[f71,f63])).
% 0.13/0.46  fof(f63,plain,(
% 0.13/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f23])).
% 0.13/0.46  fof(f23,plain,(
% 0.13/0.46    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(flattening,[],[f22])).
% 0.13/0.46  fof(f22,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(ennf_transformation,[],[f13])).
% 0.13/0.46  fof(f13,axiom,(
% 0.13/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.13/0.46  fof(f71,plain,(
% 0.13/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f45])).
% 0.13/0.46  fof(f45,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.13/0.46  fof(f44,plain,(
% 0.13/0.46    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 0.13/0.46    introduced(choice_axiom,[])).
% 0.13/0.46  fof(f43,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(rectify,[],[f42])).
% 0.13/0.46  fof(f42,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(nnf_transformation,[],[f25])).
% 0.13/0.46  fof(f25,plain,(
% 0.13/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.13/0.46    inference(ennf_transformation,[],[f11])).
% 0.13/0.46  fof(f11,axiom,(
% 0.13/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.13/0.46  fof(f206,plain,(
% 0.13/0.46    spl5_1 | ~spl5_2),
% 0.13/0.46    inference(avatar_contradiction_clause,[],[f205])).
% 0.13/0.46  fof(f205,plain,(
% 0.13/0.46    $false | (spl5_1 | ~spl5_2)),
% 0.13/0.46    inference(subsumption_resolution,[],[f204,f82])).
% 0.13/0.46  fof(f82,plain,(
% 0.13/0.46    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl5_1),
% 0.13/0.46    inference(avatar_component_clause,[],[f80])).
% 0.13/0.46  fof(f204,plain,(
% 0.13/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl5_2),
% 0.13/0.46    inference(forward_demodulation,[],[f203,f183])).
% 0.13/0.46  fof(f183,plain,(
% 0.13/0.46    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 0.13/0.46    inference(resolution,[],[f167,f46])).
% 0.13/0.46  fof(f167,plain,(
% 0.13/0.46    ( ! [X4] : (~v1_relat_1(X4) | k1_xboole_0 = k10_relat_1(X4,k1_xboole_0)) )),
% 0.13/0.46    inference(resolution,[],[f161,f139])).
% 0.13/0.46  fof(f139,plain,(
% 0.13/0.46    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.13/0.46    inference(resolution,[],[f136,f77])).
% 0.13/0.46  % (7194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.13/0.46  fof(f77,plain,(
% 0.13/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.13/0.46    inference(equality_resolution,[],[f58])).
% 0.13/0.46  fof(f58,plain,(
% 0.13/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.13/0.46    inference(cnf_transformation,[],[f36])).
% 0.13/0.46  fof(f36,plain,(
% 0.13/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.13/0.46    inference(flattening,[],[f35])).
% 0.13/0.46  fof(f35,plain,(
% 0.13/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.13/0.46    inference(nnf_transformation,[],[f4])).
% 0.13/0.46  fof(f4,axiom,(
% 0.13/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.13/0.46  fof(f136,plain,(
% 0.13/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_xboole_0 = X1 | ~r1_xboole_0(X0,X1)) )),
% 0.13/0.46    inference(resolution,[],[f72,f77])).
% 0.13/0.46  fof(f72,plain,(
% 0.13/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f27])).
% 0.13/0.46  fof(f27,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.13/0.46    inference(flattening,[],[f26])).
% 0.13/0.46  fof(f26,plain,(
% 0.13/0.46    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.13/0.46    inference(ennf_transformation,[],[f6])).
% 0.13/0.46  % (7207)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.13/0.46  fof(f6,axiom,(
% 0.13/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.13/0.46  fof(f161,plain,(
% 0.13/0.46    ( ! [X0,X1] : (r1_xboole_0(k10_relat_1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0)) )),
% 0.13/0.46    inference(resolution,[],[f158,f52])).
% 0.13/0.46  fof(f158,plain,(
% 0.13/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1)) )),
% 0.13/0.46    inference(resolution,[],[f70,f93])).
% 0.13/0.46  fof(f70,plain,(
% 0.13/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f45])).
% 0.13/0.46  fof(f203,plain,(
% 0.13/0.46    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | ~spl5_2),
% 0.13/0.46    inference(superposition,[],[f176,f116])).
% 0.13/0.46  fof(f116,plain,(
% 0.13/0.46    k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)) | ~spl5_2),
% 0.13/0.46    inference(resolution,[],[f76,f85])).
% 0.13/0.46  fof(f85,plain,(
% 0.13/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl5_2),
% 0.13/0.46    inference(avatar_component_clause,[],[f84])).
% 0.13/0.46  fof(f76,plain,(
% 0.13/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.13/0.46    inference(definition_unfolding,[],[f60,f51])).
% 0.13/0.46  fof(f51,plain,(
% 0.13/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.13/0.46    inference(cnf_transformation,[],[f8])).
% 0.13/0.46  fof(f8,axiom,(
% 0.13/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.13/0.46  fof(f60,plain,(
% 0.13/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f37])).
% 0.13/0.46  fof(f37,plain,(
% 0.13/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.13/0.46    inference(nnf_transformation,[],[f1])).
% 0.13/0.46  fof(f1,axiom,(
% 0.13/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.13/0.46  fof(f176,plain,(
% 0.13/0.46    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) )),
% 0.13/0.46    inference(resolution,[],[f74,f46])).
% 0.13/0.46  fof(f74,plain,(
% 0.13/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 0.13/0.46    inference(definition_unfolding,[],[f55,f51])).
% 0.13/0.46  fof(f55,plain,(
% 0.13/0.46    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.13/0.46    inference(cnf_transformation,[],[f20])).
% 0.13/0.46  fof(f20,plain,(
% 0.13/0.46    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.46    inference(ennf_transformation,[],[f12])).
% 0.13/0.46  fof(f12,axiom,(
% 0.13/0.46    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.13/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.13/0.47  fof(f88,plain,(
% 0.13/0.47    spl5_1 | spl5_2),
% 0.13/0.47    inference(avatar_split_clause,[],[f47,f84,f80])).
% 0.13/0.47  fof(f47,plain,(
% 0.13/0.47    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.13/0.47    inference(cnf_transformation,[],[f32])).
% 0.13/0.47  fof(f87,plain,(
% 0.13/0.47    ~spl5_1 | ~spl5_2),
% 0.13/0.47    inference(avatar_split_clause,[],[f48,f84,f80])).
% 0.13/0.47  fof(f48,plain,(
% 0.13/0.47    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.13/0.47    inference(cnf_transformation,[],[f32])).
% 0.13/0.47  % SZS output end Proof for theBenchmark
% 0.13/0.47  % (7184)------------------------------
% 0.13/0.47  % (7184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.47  % (7184)Termination reason: Refutation
% 0.13/0.47  
% 0.13/0.47  % (7184)Memory used [KB]: 11129
% 0.13/0.47  % (7184)Time elapsed: 0.111 s
% 0.13/0.47  % (7194)Refutation not found, incomplete strategy% (7194)------------------------------
% 0.13/0.47  % (7194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.47  % (7194)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.47  
% 0.13/0.47  % (7194)Memory used [KB]: 10618
% 0.13/0.47  % (7194)Time elapsed: 0.145 s
% 0.13/0.47  % (7194)------------------------------
% 0.13/0.47  % (7194)------------------------------
% 0.13/0.47  % (7184)------------------------------
% 0.13/0.47  % (7184)------------------------------
% 0.13/0.47  % (7186)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.13/0.47  % (7177)Success in time 0.184 s
%------------------------------------------------------------------------------
