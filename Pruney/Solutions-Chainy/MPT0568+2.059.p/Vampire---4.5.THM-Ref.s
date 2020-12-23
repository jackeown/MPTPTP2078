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
% DateTime   : Thu Dec  3 12:50:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 110 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 285 expanded)
%              Number of equality atoms :   83 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f171,f274,f296,f313])).

fof(f313,plain,
    ( ~ spl3_5
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl3_5
    | spl3_10 ),
    inference(subsumption_resolution,[],[f310,f156])).

fof(f156,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f310,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_10 ),
    inference(trivial_inequality_removal,[],[f309])).

fof(f309,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | spl3_10 ),
    inference(superposition,[],[f295,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f295,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl3_10
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f296,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f289,f169,f86,f293])).

fof(f86,plain,
    ( spl3_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f169,plain,
    ( spl3_7
  <=> ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f289,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f88,f170])).

fof(f170,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f88,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f274,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f253,f219])).

fof(f219,plain,
    ( ! [X0] : sK2(k1_xboole_0) = X0
    | spl3_5 ),
    inference(resolution,[],[f191,f84])).

fof(f84,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f191,plain,
    ( ! [X0] : r2_hidden(sK2(k1_xboole_0),X0)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f190,f155])).

fof(f155,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f190,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0),X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f122,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f253,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0)
    | spl3_5 ),
    inference(superposition,[],[f105,f219])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(forward_demodulation,[],[f81,f100])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f81,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

% (14182)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f171,plain,
    ( ~ spl3_5
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f167,f91,f169,f154])).

fof(f91,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f167,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f166,f110])).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f60,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f166,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_2 ),
    inference(superposition,[],[f64,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f94,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f77,f91])).

fof(f77,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f89,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f39])).

fof(f39,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (14176)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (14193)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.51  % (14184)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.51  % (14201)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (14183)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.51  % (14201)Refutation not found, incomplete strategy% (14201)------------------------------
% 0.19/0.51  % (14201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (14201)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (14201)Memory used [KB]: 1663
% 0.19/0.51  % (14201)Time elapsed: 0.104 s
% 0.19/0.51  % (14201)------------------------------
% 0.19/0.51  % (14201)------------------------------
% 0.19/0.51  % (14179)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.51  % (14194)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (14185)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (14193)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f314,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f89,f94,f171,f274,f296,f313])).
% 0.19/0.52  fof(f313,plain,(
% 0.19/0.52    ~spl3_5 | spl3_10),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f312])).
% 0.19/0.52  fof(f312,plain,(
% 0.19/0.52    $false | (~spl3_5 | spl3_10)),
% 0.19/0.52    inference(subsumption_resolution,[],[f310,f156])).
% 0.19/0.52  fof(f156,plain,(
% 0.19/0.52    v1_relat_1(k1_xboole_0) | ~spl3_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f154])).
% 0.19/0.52  fof(f154,plain,(
% 0.19/0.52    spl3_5 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.52  fof(f310,plain,(
% 0.19/0.52    ~v1_relat_1(k1_xboole_0) | spl3_10),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f309])).
% 0.19/0.52  fof(f309,plain,(
% 0.19/0.52    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | spl3_10),
% 0.19/0.52    inference(superposition,[],[f295,f65])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.19/0.52  fof(f295,plain,(
% 0.19/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | spl3_10),
% 0.19/0.52    inference(avatar_component_clause,[],[f293])).
% 0.19/0.52  fof(f293,plain,(
% 0.19/0.52    spl3_10 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.52  fof(f296,plain,(
% 0.19/0.52    ~spl3_10 | spl3_1 | ~spl3_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f289,f169,f86,f293])).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    spl3_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.52  fof(f169,plain,(
% 0.19/0.52    spl3_7 <=> ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.52  fof(f289,plain,(
% 0.19/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | (spl3_1 | ~spl3_7)),
% 0.19/0.52    inference(superposition,[],[f88,f170])).
% 0.19/0.52  fof(f170,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | ~spl3_7),
% 0.19/0.52    inference(avatar_component_clause,[],[f169])).
% 0.19/0.52  fof(f88,plain,(
% 0.19/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl3_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f86])).
% 0.19/0.52  fof(f274,plain,(
% 0.19/0.52    spl3_5),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f273])).
% 0.19/0.52  fof(f273,plain,(
% 0.19/0.52    $false | spl3_5),
% 0.19/0.52    inference(subsumption_resolution,[],[f253,f219])).
% 0.19/0.52  fof(f219,plain,(
% 0.19/0.52    ( ! [X0] : (sK2(k1_xboole_0) = X0) ) | spl3_5),
% 0.19/0.52    inference(resolution,[],[f191,f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.19/0.52    inference(equality_resolution,[],[f56])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(rectify,[],[f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.52  fof(f191,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0),X0)) ) | spl3_5),
% 0.19/0.52    inference(subsumption_resolution,[],[f190,f155])).
% 0.19/0.52  fof(f155,plain,(
% 0.19/0.52    ~v1_relat_1(k1_xboole_0) | spl3_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f154])).
% 0.19/0.52  fof(f190,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0),X0) | v1_relat_1(k1_xboole_0)) )),
% 0.19/0.52    inference(resolution,[],[f122,f78])).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f48])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.19/0.52    inference(unused_predicate_definition_removal,[],[f21])).
% 0.19/0.52  fof(f21,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.19/0.52  fof(f122,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 0.19/0.52    inference(resolution,[],[f75,f66])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,axiom,(
% 0.19/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.52  fof(f75,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,axiom,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.52  fof(f253,plain,(
% 0.19/0.52    k1_xboole_0 != sK2(k1_xboole_0) | spl3_5),
% 0.19/0.52    inference(superposition,[],[f105,f219])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f81,f100])).
% 0.19/0.52  fof(f100,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.52    inference(superposition,[],[f61,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.19/0.52    inference(equality_resolution,[],[f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.19/0.52    inference(nnf_transformation,[],[f15])).
% 0.19/0.52  % (14182)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.52  fof(f171,plain,(
% 0.19/0.52    ~spl3_5 | spl3_7 | ~spl3_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f167,f91,f169,f154])).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    spl3_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.52  fof(f167,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl3_2),
% 0.19/0.52    inference(forward_demodulation,[],[f166,f110])).
% 0.19/0.52  fof(f110,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.52    inference(superposition,[],[f60,f63])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.52  fof(f166,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl3_2),
% 0.19/0.52    inference(superposition,[],[f64,f93])).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_2),
% 0.19/0.52    inference(avatar_component_clause,[],[f91])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    spl3_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f77,f91])).
% 0.19/0.52  fof(f77,plain,(
% 0.19/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,axiom,(
% 0.19/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.52  fof(f89,plain,(
% 0.19/0.52    ~spl3_1),
% 0.19/0.52    inference(avatar_split_clause,[],[f49,f86])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.19/0.52    inference(ennf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,negated_conjecture,(
% 0.19/0.52    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.19/0.52    inference(negated_conjecture,[],[f25])).
% 0.19/0.52  fof(f25,conjecture,(
% 0.19/0.52    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (14193)------------------------------
% 0.19/0.52  % (14193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14193)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (14193)Memory used [KB]: 6396
% 0.19/0.52  % (14193)Time elapsed: 0.112 s
% 0.19/0.52  % (14193)------------------------------
% 0.19/0.52  % (14193)------------------------------
% 0.19/0.52  % (14177)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (14172)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (14172)Refutation not found, incomplete strategy% (14172)------------------------------
% 0.19/0.52  % (14172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14172)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (14172)Memory used [KB]: 1663
% 0.19/0.52  % (14172)Time elapsed: 0.116 s
% 0.19/0.52  % (14172)------------------------------
% 0.19/0.52  % (14172)------------------------------
% 0.19/0.53  % (14169)Success in time 0.173 s
%------------------------------------------------------------------------------
