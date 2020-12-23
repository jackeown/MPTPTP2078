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
% DateTime   : Thu Dec  3 12:51:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 118 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  191 ( 343 expanded)
%              Number of equality atoms :   82 ( 166 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f283,f288])).

fof(f288,plain,
    ( spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f286,f55,f63])).

fof(f63,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( spl3_2
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f286,plain,
    ( k1_xboole_0 = sK0
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK0
    | spl3_2 ),
    inference(superposition,[],[f56,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f161,f86])).

fof(f86,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k2_relat_1(k2_zfmisc_1(X6,X5)))
      | k2_relat_1(k2_zfmisc_1(X6,X5)) = X5 ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

% (1156)Refutation not found, incomplete strategy% (1156)------------------------------
% (1156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1156)Termination reason: Refutation not found, incomplete strategy

% (1156)Memory used [KB]: 10618
% (1156)Time elapsed: 0.123 s
% (1156)------------------------------
% (1156)------------------------------
fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

% (1161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f161,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X1 ) ),
    inference(global_subsumption,[],[f35,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X1
      | ~ v1_relat_1(k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f149,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f149,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X7,X5),k2_zfmisc_1(X8,X6))
      | r1_tarski(X5,X6)
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f127,f141])).

fof(f141,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f39,f66])).

fof(f66,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

% (1157)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

% (1143)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (1161)Refutation not found, incomplete strategy% (1161)------------------------------
% (1161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (1168)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (1145)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (1151)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (1137)Refutation not found, incomplete strategy% (1137)------------------------------
% (1137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1165)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | r1_tarski(X1,X3)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f283,plain,
    ( spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f281,f52,f59])).

fof(f59,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( spl3_1
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f281,plain,
    ( k1_xboole_0 = sK1
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1
    | spl3_1 ),
    inference(superposition,[],[f53,f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X1,X0)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f265,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(k2_zfmisc_1(X1,X2)) = X1 ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f265,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f257,f35])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f151,f33])).

fof(f151,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8))
      | r1_tarski(X5,X6)
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f128,f141])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,X1)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f32,f34])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f65,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
        | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f61,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f30,f55,f52])).

fof(f30,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:38:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (1139)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (1147)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (1141)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1135)Refutation not found, incomplete strategy% (1135)------------------------------
% 0.21/0.51  % (1135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1135)Memory used [KB]: 1663
% 0.21/0.51  % (1135)Time elapsed: 0.091 s
% 0.21/0.51  % (1135)------------------------------
% 0.21/0.51  % (1135)------------------------------
% 0.21/0.52  % (1158)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (1144)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (1136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (1148)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1146)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (1142)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1154)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (1160)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (1164)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (1169)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (1158)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (1144)Refutation not found, incomplete strategy% (1144)------------------------------
% 0.21/0.54  % (1144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1144)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1144)Memory used [KB]: 10618
% 0.21/0.54  % (1144)Time elapsed: 0.122 s
% 0.21/0.54  % (1144)------------------------------
% 0.21/0.54  % (1144)------------------------------
% 1.37/0.54  % (1140)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (1150)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.54  % (1160)Refutation not found, incomplete strategy% (1160)------------------------------
% 1.37/0.54  % (1160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (1160)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (1160)Memory used [KB]: 1663
% 1.37/0.54  % (1160)Time elapsed: 0.128 s
% 1.37/0.54  % (1160)------------------------------
% 1.37/0.54  % (1160)------------------------------
% 1.37/0.54  % (1166)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.55  % (1156)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.55  % SZS output start Proof for theBenchmark
% 1.37/0.55  fof(f289,plain,(
% 1.37/0.55    $false),
% 1.37/0.55    inference(avatar_sat_refutation,[],[f57,f61,f65,f283,f288])).
% 1.37/0.55  fof(f288,plain,(
% 1.37/0.55    spl3_4 | spl3_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f286,f55,f63])).
% 1.37/0.55  fof(f63,plain,(
% 1.37/0.55    spl3_4 <=> k1_xboole_0 = sK0),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.37/0.55  fof(f55,plain,(
% 1.37/0.55    spl3_2 <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.55  fof(f286,plain,(
% 1.37/0.55    k1_xboole_0 = sK0 | spl3_2),
% 1.37/0.55    inference(trivial_inequality_removal,[],[f285])).
% 1.37/0.55  fof(f285,plain,(
% 1.37/0.55    sK1 != sK1 | k1_xboole_0 = sK0 | spl3_2),
% 1.37/0.55    inference(superposition,[],[f56,f174])).
% 1.37/0.55  fof(f174,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X0) )),
% 1.37/0.55    inference(resolution,[],[f161,f86])).
% 1.37/0.55  fof(f86,plain,(
% 1.37/0.55    ( ! [X6,X5] : (~r1_tarski(X5,k2_relat_1(k2_zfmisc_1(X6,X5))) | k2_relat_1(k2_zfmisc_1(X6,X5)) = X5) )),
% 1.37/0.55    inference(resolution,[],[f43,f38])).
% 1.37/0.55  fof(f38,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 1.37/0.55  % (1156)Refutation not found, incomplete strategy% (1156)------------------------------
% 1.37/0.55  % (1156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (1156)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (1156)Memory used [KB]: 10618
% 1.37/0.55  % (1156)Time elapsed: 0.123 s
% 1.37/0.55  % (1156)------------------------------
% 1.37/0.55  % (1156)------------------------------
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  % (1161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.55  fof(f25,plain,(
% 1.37/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.55    inference(flattening,[],[f24])).
% 1.37/0.55  fof(f24,plain,(
% 1.37/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.55    inference(nnf_transformation,[],[f3])).
% 1.37/0.55  fof(f3,axiom,(
% 1.37/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.55  fof(f161,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X1) )),
% 1.37/0.55    inference(global_subsumption,[],[f35,f155])).
% 1.37/0.55  fof(f155,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X1 | ~v1_relat_1(k2_zfmisc_1(X1,X0))) )),
% 1.37/0.55    inference(resolution,[],[f149,f33])).
% 1.37/0.55  fof(f33,plain,(
% 1.37/0.55    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f16])).
% 1.37/0.55  fof(f16,plain,(
% 1.37/0.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f10])).
% 1.37/0.55  fof(f10,axiom,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.37/0.55  fof(f149,plain,(
% 1.37/0.55    ( ! [X6,X8,X7,X5] : (~r1_tarski(k2_zfmisc_1(X7,X5),k2_zfmisc_1(X8,X6)) | r1_tarski(X5,X6) | k1_xboole_0 = X7) )),
% 1.37/0.55    inference(resolution,[],[f127,f141])).
% 1.37/0.55  fof(f141,plain,(
% 1.37/0.55    ( ! [X0] : (r2_hidden(sK2(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.37/0.55    inference(resolution,[],[f39,f66])).
% 1.37/0.55  fof(f66,plain,(
% 1.37/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.37/0.55    inference(superposition,[],[f36,f49])).
% 1.37/0.55  fof(f49,plain,(
% 1.37/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.37/0.55    inference(equality_resolution,[],[f46])).
% 1.37/0.55  fof(f46,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.37/0.55    inference(cnf_transformation,[],[f27])).
% 1.37/0.55  fof(f27,plain,(
% 1.37/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.37/0.55    inference(flattening,[],[f26])).
% 1.37/0.55  fof(f26,plain,(
% 1.37/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.37/0.55    inference(nnf_transformation,[],[f4])).
% 1.37/0.55  fof(f4,axiom,(
% 1.37/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.37/0.55  fof(f36,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f6])).
% 1.37/0.55  % (1157)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  fof(f6,axiom,(
% 1.37/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.37/0.55  fof(f39,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f23])).
% 1.37/0.55  fof(f23,plain,(
% 1.37/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.37/0.55  % (1143)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.55  % (1161)Refutation not found, incomplete strategy% (1161)------------------------------
% 1.37/0.55  % (1161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (1137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.55  % (1168)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (1145)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.55  % (1151)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (1137)Refutation not found, incomplete strategy% (1137)------------------------------
% 1.37/0.55  % (1137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (1165)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.56  fof(f22,plain,(
% 1.37/0.56    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f21,plain,(
% 1.37/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.37/0.56    inference(nnf_transformation,[],[f18])).
% 1.37/0.56  fof(f18,plain,(
% 1.37/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.37/0.56    inference(ennf_transformation,[],[f2])).
% 1.37/0.56  fof(f2,axiom,(
% 1.37/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.37/0.56  fof(f127,plain,(
% 1.37/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,X0) | r1_tarski(X1,X3) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.37/0.56    inference(resolution,[],[f31,f34])).
% 1.37/0.56  fof(f34,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f17])).
% 1.37/0.56  fof(f17,plain,(
% 1.37/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f13])).
% 1.37/0.56  fof(f13,plain,(
% 1.37/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.37/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.37/0.56  fof(f1,axiom,(
% 1.37/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | r1_tarski(X1,X3)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f15])).
% 1.37/0.56  fof(f15,plain,(
% 1.37/0.56    ! [X0] : (! [X1,X2,X3] : (r1_tarski(X1,X3) | (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) & ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) | v1_xboole_0(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f5])).
% 1.37/0.56  fof(f5,axiom,(
% 1.37/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 1.37/0.56  fof(f35,plain,(
% 1.37/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f7])).
% 1.37/0.56  fof(f7,axiom,(
% 1.37/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.37/0.56  fof(f56,plain,(
% 1.37/0.56    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_2),
% 1.37/0.56    inference(avatar_component_clause,[],[f55])).
% 1.37/0.56  fof(f283,plain,(
% 1.37/0.56    spl3_3 | spl3_1),
% 1.37/0.56    inference(avatar_split_clause,[],[f281,f52,f59])).
% 1.37/0.56  fof(f59,plain,(
% 1.37/0.56    spl3_3 <=> k1_xboole_0 = sK1),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.37/0.56  fof(f52,plain,(
% 1.37/0.56    spl3_1 <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.56  fof(f281,plain,(
% 1.37/0.56    k1_xboole_0 = sK1 | spl3_1),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f275])).
% 1.37/0.56  fof(f275,plain,(
% 1.37/0.56    sK0 != sK0 | k1_xboole_0 = sK1 | spl3_1),
% 1.37/0.56    inference(superposition,[],[f53,f268])).
% 1.37/0.56  fof(f268,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X1,X0)) = X1 | k1_xboole_0 = X0) )),
% 1.37/0.56    inference(resolution,[],[f265,f83])).
% 1.37/0.56  fof(f83,plain,(
% 1.37/0.56    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(k2_zfmisc_1(X1,X2)) = X1) )),
% 1.37/0.56    inference(resolution,[],[f43,f37])).
% 1.37/0.56  fof(f37,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f8])).
% 1.37/0.56  fof(f8,axiom,(
% 1.37/0.56    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 1.37/0.56  fof(f265,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0) )),
% 1.37/0.56    inference(resolution,[],[f257,f35])).
% 1.37/0.56  fof(f257,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~v1_relat_1(k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.56    inference(resolution,[],[f151,f33])).
% 1.37/0.56  fof(f151,plain,(
% 1.37/0.56    ( ! [X6,X8,X7,X5] : (~r1_tarski(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)) | r1_tarski(X5,X6) | k1_xboole_0 = X7) )),
% 1.37/0.56    inference(resolution,[],[f128,f141])).
% 1.37/0.56  fof(f128,plain,(
% 1.37/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,X1) | r1_tarski(X0,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.37/0.56    inference(resolution,[],[f32,f34])).
% 1.37/0.56  fof(f32,plain,(
% 1.37/0.56    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(X1,X3)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f15])).
% 1.37/0.56  fof(f53,plain,(
% 1.37/0.56    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 1.37/0.56    inference(avatar_component_clause,[],[f52])).
% 1.37/0.56  fof(f65,plain,(
% 1.37/0.56    ~spl3_4),
% 1.37/0.56    inference(avatar_split_clause,[],[f28,f63])).
% 1.37/0.56  fof(f28,plain,(
% 1.37/0.56    k1_xboole_0 != sK0),
% 1.37/0.56    inference(cnf_transformation,[],[f20])).
% 1.37/0.56  fof(f20,plain,(
% 1.37/0.56    (sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.37/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 1.37/0.56  fof(f19,plain,(
% 1.37/0.56    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => ((sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.37/0.56    introduced(choice_axiom,[])).
% 1.37/0.56  fof(f14,plain,(
% 1.37/0.56    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.37/0.56    inference(ennf_transformation,[],[f12])).
% 1.37/0.56  fof(f12,negated_conjecture,(
% 1.37/0.56    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.37/0.56    inference(negated_conjecture,[],[f11])).
% 1.37/0.56  fof(f11,conjecture,(
% 1.37/0.56    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.37/0.56  fof(f61,plain,(
% 1.37/0.56    ~spl3_3),
% 1.37/0.56    inference(avatar_split_clause,[],[f29,f59])).
% 1.37/0.56  fof(f29,plain,(
% 1.37/0.56    k1_xboole_0 != sK1),
% 1.37/0.56    inference(cnf_transformation,[],[f20])).
% 1.37/0.56  fof(f57,plain,(
% 1.37/0.56    ~spl3_1 | ~spl3_2),
% 1.37/0.56    inference(avatar_split_clause,[],[f30,f55,f52])).
% 1.37/0.56  fof(f30,plain,(
% 1.37/0.56    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.37/0.56    inference(cnf_transformation,[],[f20])).
% 1.37/0.56  % SZS output end Proof for theBenchmark
% 1.37/0.56  % (1158)------------------------------
% 1.37/0.56  % (1158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (1158)Termination reason: Refutation
% 1.37/0.56  
% 1.37/0.56  % (1158)Memory used [KB]: 10874
% 1.37/0.56  % (1158)Time elapsed: 0.128 s
% 1.37/0.56  % (1158)------------------------------
% 1.37/0.56  % (1158)------------------------------
% 1.37/0.56  % (1137)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (1137)Memory used [KB]: 10618
% 1.53/0.56  % (1131)Success in time 0.195 s
%------------------------------------------------------------------------------
