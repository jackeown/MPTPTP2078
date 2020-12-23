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
% DateTime   : Thu Dec  3 12:46:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 142 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 ( 487 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f193,f249])).

fof(f249,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f245,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 = k7_setfam_1(sK5,sK6)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f11,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK5,sK6)
      & k1_xboole_0 != sK6
      & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f245,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_3 ),
    inference(resolution,[],[f242,f151])).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f94])).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f91,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f91,plain,(
    ! [X4,X3] :
      ( sP3(X4,X3,k1_xboole_0)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f64,f75])).

fof(f75,plain,(
    ! [X0] : sP4(k1_xboole_0,X0,k1_xboole_0) ),
    inference(superposition,[],[f74,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f74,plain,(
    ! [X0,X1] : sP4(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f22,f21])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP3(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP3(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP3(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (12978)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X3,X0) )
            & ( sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK8(X0,X1),X1)
          | ~ r2_hidden(sK8(X0,X1),X0) )
        & ( r2_hidden(sK8(X0,X1),X1)
          | r2_hidden(sK8(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1),X1)
          | ~ r2_hidden(sK8(X0,X1),X0) )
        & ( r2_hidden(sK8(X0,X1),X1)
          | r2_hidden(sK8(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f241,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK5))
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f241,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
        | ~ r2_hidden(X0,sK6) )
    | ~ spl10_3 ),
    inference(resolution,[],[f235,f122])).

fof(f122,plain,
    ( sP1(sK6,sK5,k1_xboole_0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl10_3
  <=> sP1(sK6,sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X2,k1_xboole_0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f139,f94])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_subset_1(X2,X0),X3)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ sP1(X1,X2,X3) ) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X2,X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(X2,sK7(X0,X1,X2),X1,X0)
          & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X2,X3,X1,X0)
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ~ sP0(X2,sK7(X0,X1,X2),X1,X0)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X3,X1,X0)
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X3] :
            ( ~ sP0(X1,X3,X0,X2)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( sP0(X1,X3,X0,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ! [X3] :
          ( sP0(X1,X3,X0,X2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k3_subset_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | r2_hidden(X1,X3) ) ) )
      & ( ( ( r2_hidden(X1,X3)
            | ~ r2_hidden(k3_subset_1(X2,X1),X0) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X3,X0,X2] :
      ( ( sP0(X1,X3,X0,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) ) ) )
      & ( ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X3,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X1,X3,X0,X2] :
      ( sP0(X1,X3,X0,X2)
    <=> ( r2_hidden(X3,X2)
      <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f193,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f186,f124])).

fof(f124,plain,
    ( spl10_4
  <=> sP2(k1_xboole_0,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f186,plain,(
    sP2(k1_xboole_0,sK5,sK6) ),
    inference(resolution,[],[f182,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f182,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK5)))
      | sP2(X2,sK5,sK6) ) ),
    inference(resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP2(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP2(X1,X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f13,f19,f18,f17])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f127,plain,
    ( spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f108,f124,f120])).

fof(f108,plain,
    ( ~ sP2(k1_xboole_0,sK5,sK6)
    | sP1(sK6,sK5,k1_xboole_0) ),
    inference(superposition,[],[f73,f105])).

fof(f105,plain,(
    sK6 = k7_setfam_1(sK5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,
    ( sK6 = k7_setfam_1(sK5,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5))) ),
    inference(superposition,[],[f50,f47])).

fof(f47,plain,(
    k1_xboole_0 = k7_setfam_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1,k7_setfam_1(X1,X0))
      | sP1(k7_setfam_1(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k7_setfam_1(X1,X0) != X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X0) = X2
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k7_setfam_1(X1,X0) != X2 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP1(X2,X0,X1) )
        & ( sP1(X2,X0,X1)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP2(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (12951)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (12953)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (12977)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.50  % (12948)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (12952)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (12948)Refutation not found, incomplete strategy% (12948)------------------------------
% 0.20/0.51  % (12948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12948)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12948)Memory used [KB]: 1663
% 0.20/0.51  % (12948)Time elapsed: 0.099 s
% 0.20/0.51  % (12948)------------------------------
% 0.20/0.51  % (12948)------------------------------
% 0.20/0.51  % (12952)Refutation not found, incomplete strategy% (12952)------------------------------
% 0.20/0.51  % (12952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12952)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12952)Memory used [KB]: 6140
% 0.20/0.51  % (12952)Time elapsed: 0.099 s
% 0.20/0.51  % (12952)------------------------------
% 0.20/0.51  % (12952)------------------------------
% 0.20/0.51  % (12949)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (12970)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (12962)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (12969)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (12971)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (12979)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (12960)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (12955)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12959)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (12960)Refutation not found, incomplete strategy% (12960)------------------------------
% 0.20/0.52  % (12960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12960)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12960)Memory used [KB]: 10618
% 0.20/0.52  % (12960)Time elapsed: 0.117 s
% 0.20/0.52  % (12960)------------------------------
% 0.20/0.52  % (12960)------------------------------
% 0.20/0.52  % (12959)Refutation not found, incomplete strategy% (12959)------------------------------
% 0.20/0.52  % (12959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12959)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12959)Memory used [KB]: 10618
% 0.20/0.52  % (12959)Time elapsed: 0.110 s
% 0.20/0.52  % (12959)------------------------------
% 0.20/0.52  % (12959)------------------------------
% 0.20/0.52  % (12971)Refutation not found, incomplete strategy% (12971)------------------------------
% 0.20/0.52  % (12971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12973)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (12968)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (12967)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (12957)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (12977)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (12961)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f127,f193,f249])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    ~spl10_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f248])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    $false | ~spl10_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f245,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    k1_xboole_0 != sK6),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    k1_xboole_0 = k7_setfam_1(sK5,sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f11,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK5,sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    k1_xboole_0 = sK6 | ~spl10_3),
% 0.20/0.53    inference(resolution,[],[f242,f151])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK8(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(resolution,[],[f61,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(condensation,[],[f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f91,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP3(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 0.20/0.53    inference(flattening,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X1,X3,X0] : (sP3(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X4,X3] : (sP3(X4,X3,k1_xboole_0) | ~r2_hidden(X3,k1_xboole_0)) )),
% 0.20/0.53    inference(resolution,[],[f64,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X0] : (sP4(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.53    inference(superposition,[],[f74,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP4(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP4(X0,X1,X2)) & (sP4(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP4(X0,X1,X2))),
% 0.20/0.53    inference(definition_folding,[],[f1,f22,f21])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (sP4(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP3(X1,X3,X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r2_hidden(X4,X2) | sP3(X1,X4,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ((~sP3(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP3(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP3(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP3(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  % (12978)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP3(X1,X3,X0)) & (sP3(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f22])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | X0 = X1 | r2_hidden(sK8(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK8(X0,X1),X1) | ~r2_hidden(sK8(X0,X1),X0)) & (r2_hidden(sK8(X0,X1),X1) | r2_hidden(sK8(X0,X1),X0))))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK8(X0,X1),X1) | ~r2_hidden(sK8(X0,X1),X0)) & (r2_hidden(sK8(X0,X1),X1) | r2_hidden(sK8(X0,X1),X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.20/0.53    inference(nnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK6)) ) | ~spl10_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f241,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK5)) | ~r2_hidden(X0,sK6)) )),
% 0.20/0.53    inference(resolution,[],[f63,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5)))),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK5)) | ~r2_hidden(X0,sK6)) ) | ~spl10_3),
% 0.20/0.53    inference(resolution,[],[f235,f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    sP1(sK6,sK5,k1_xboole_0) | ~spl10_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    spl10_3 <=> sP1(sK6,sK5,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP1(X1,X2,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f139,f94])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_subset_1(X2,X0),X3) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~sP1(X1,X2,X3)) )),
% 0.20/0.53    inference(resolution,[],[f56,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~sP1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~sP0(X2,sK7(X0,X1,X2),X1,X0) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1))) => (~sP0(X2,sK7(X0,X1,X2),X1,X0) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ? [X3] : (~sP0(X1,X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP1(X2,X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> ! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | ~r2_hidden(X1,X3) | r2_hidden(k3_subset_1(X2,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3)) & (r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)))) & (((r2_hidden(X1,X3) | ~r2_hidden(k3_subset_1(X2,X1),X0)) & (r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.53    inference(rectify,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X1,X3,X0,X2] : ((sP0(X1,X3,X0,X2) | ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)))) & (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~sP0(X1,X3,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X1,X3,X0,X2] : (sP0(X1,X3,X0,X2) <=> (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    spl10_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f186,f124])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    spl10_4 <=> sP2(k1_xboole_0,sK5,sK6)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    sP2(k1_xboole_0,sK5,sK6)),
% 0.20/0.53    inference(resolution,[],[f182,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK5))) | sP2(X2,sK5,sK6)) )),
% 0.20/0.53    inference(resolution,[],[f60,f45])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP2(X1,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (sP2(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(definition_folding,[],[f13,f19,f18,f17])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((k7_setfam_1(X0,X1) = X2 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0,X2))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl10_3 | ~spl10_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f108,f124,f120])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ~sP2(k1_xboole_0,sK5,sK6) | sP1(sK6,sK5,k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f73,f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    sK6 = k7_setfam_1(sK5,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f104,f45])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    sK6 = k7_setfam_1(sK5,k1_xboole_0) | ~m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK5)))),
% 0.20/0.53    inference(superposition,[],[f50,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    k1_xboole_0 = k7_setfam_1(sK5,sK6)),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~sP2(X0,X1,k7_setfam_1(X1,X0)) | sP1(k7_setfam_1(X1,X0),X1,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2 | ~sP2(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2)) | ~sP2(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (((k7_setfam_1(X0,X1) = X2 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k7_setfam_1(X0,X1) != X2)) | ~sP2(X1,X0,X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (12977)------------------------------
% 0.20/0.53  % (12977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12977)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (12977)Memory used [KB]: 6268
% 0.20/0.53  % (12977)Time elapsed: 0.116 s
% 0.20/0.53  % (12977)------------------------------
% 0.20/0.53  % (12977)------------------------------
% 0.20/0.53  % (12944)Success in time 0.176 s
%------------------------------------------------------------------------------
