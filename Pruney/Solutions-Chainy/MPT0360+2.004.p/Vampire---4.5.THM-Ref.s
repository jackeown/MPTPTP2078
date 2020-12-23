%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:48 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 122 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  153 ( 308 expanded)
%              Number of equality atoms :   50 (  97 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f268,f270,f323])).

fof(f323,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f321])).

fof(f321,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2 ),
    inference(superposition,[],[f31,f291])).

fof(f291,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f58,f290])).

fof(f290,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f285,f274])).

fof(f274,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f273,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f273,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f267,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (12121)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f267,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f285,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f213,f274])).

fof(f213,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f180,f190])).

fof(f190,plain,(
    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK2),k3_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f172,f38])).

fof(f172,plain,(
    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f73,f164])).

fof(f164,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f73,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f180,plain,(
    ! [X2] :
      ( k1_xboole_0 != k3_xboole_0(k3_subset_1(sK0,sK2),X2)
      | k1_xboole_0 = k3_xboole_0(sK1,X2) ) ),
    inference(resolution,[],[f160,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f160,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),X1)
      | k1_xboole_0 = k3_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f98,f30])).

fof(f30,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f46,f44])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f58,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f270,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f263,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f263,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f268,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f259,f265,f261])).

fof(f259,plain,
    ( r1_tarski(sK2,sK0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f258,f48])).

fof(f48,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f258,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f200,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f200,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK2,k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK2)) ) ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (12120)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (12120)Refutation not found, incomplete strategy% (12120)------------------------------
% 0.21/0.51  % (12120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12143)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (12148)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (12120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12120)Memory used [KB]: 1663
% 0.21/0.51  % (12120)Time elapsed: 0.098 s
% 0.21/0.51  % (12120)------------------------------
% 0.21/0.51  % (12120)------------------------------
% 0.21/0.51  % (12132)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12146)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.20/0.52  % (12123)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.52  % (12131)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.52  % (12130)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.52  % (12129)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.20/0.52  % (12131)Refutation not found, incomplete strategy% (12131)------------------------------
% 1.20/0.52  % (12131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (12131)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (12131)Memory used [KB]: 10618
% 1.20/0.52  % (12131)Time elapsed: 0.110 s
% 1.20/0.52  % (12131)------------------------------
% 1.20/0.52  % (12131)------------------------------
% 1.20/0.52  % (12130)Refutation not found, incomplete strategy% (12130)------------------------------
% 1.20/0.52  % (12130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (12130)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (12130)Memory used [KB]: 10618
% 1.20/0.52  % (12130)Time elapsed: 0.119 s
% 1.20/0.52  % (12130)------------------------------
% 1.20/0.52  % (12130)------------------------------
% 1.20/0.52  % (12129)Refutation not found, incomplete strategy% (12129)------------------------------
% 1.20/0.52  % (12129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (12129)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (12129)Memory used [KB]: 10618
% 1.20/0.52  % (12129)Time elapsed: 0.118 s
% 1.20/0.52  % (12129)------------------------------
% 1.20/0.52  % (12129)------------------------------
% 1.20/0.52  % (12132)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f324,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(avatar_sat_refutation,[],[f268,f270,f323])).
% 1.20/0.52  fof(f323,plain,(
% 1.20/0.52    ~spl3_2),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f322])).
% 1.20/0.53  fof(f322,plain,(
% 1.20/0.53    $false | ~spl3_2),
% 1.20/0.53    inference(trivial_inequality_removal,[],[f321])).
% 1.20/0.53  fof(f321,plain,(
% 1.20/0.53    k1_xboole_0 != k1_xboole_0 | ~spl3_2),
% 1.20/0.53    inference(superposition,[],[f31,f291])).
% 1.20/0.53  fof(f291,plain,(
% 1.20/0.53    k1_xboole_0 = sK1 | ~spl3_2),
% 1.20/0.53    inference(backward_demodulation,[],[f58,f290])).
% 1.20/0.53  fof(f290,plain,(
% 1.20/0.53    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 1.20/0.53    inference(forward_demodulation,[],[f285,f274])).
% 1.20/0.53  fof(f274,plain,(
% 1.20/0.53    sK2 = k3_xboole_0(sK0,sK2) | ~spl3_2),
% 1.20/0.53    inference(superposition,[],[f273,f38])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.20/0.53  fof(f273,plain,(
% 1.20/0.53    sK2 = k3_xboole_0(sK2,sK0) | ~spl3_2),
% 1.20/0.53    inference(resolution,[],[f267,f41])).
% 1.20/0.53  fof(f41,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f19])).
% 1.20/0.53  fof(f19,plain,(
% 1.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f6])).
% 1.20/0.53  % (12121)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.53  fof(f6,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.20/0.53  fof(f267,plain,(
% 1.20/0.53    r1_tarski(sK2,sK0) | ~spl3_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f265])).
% 1.20/0.53  fof(f265,plain,(
% 1.20/0.53    spl3_2 <=> r1_tarski(sK2,sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.20/0.53  fof(f285,plain,(
% 1.20/0.53    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,sK2)) | ~spl3_2),
% 1.20/0.53    inference(backward_demodulation,[],[f213,f274])).
% 1.20/0.53  fof(f213,plain,(
% 1.20/0.53    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 1.20/0.53    inference(trivial_inequality_removal,[],[f208])).
% 1.20/0.53  fof(f208,plain,(
% 1.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 1.20/0.53    inference(superposition,[],[f180,f190])).
% 1.20/0.53  fof(f190,plain,(
% 1.20/0.53    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK2),k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 1.20/0.53    inference(superposition,[],[f172,f38])).
% 1.20/0.53  fof(f172,plain,(
% 1.20/0.53    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_subset_1(sK0,sK2))),
% 1.20/0.53    inference(superposition,[],[f73,f164])).
% 1.20/0.53  fof(f164,plain,(
% 1.20/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.20/0.53    inference(resolution,[],[f49,f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.20/0.53    inference(cnf_transformation,[],[f26])).
% 1.20/0.53  fof(f26,plain,(
% 1.20/0.53    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).
% 1.20/0.53  fof(f25,plain,(
% 1.20/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f18,plain,(
% 1.20/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(flattening,[],[f17])).
% 1.20/0.53  fof(f17,plain,(
% 1.20/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,negated_conjecture,(
% 1.20/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.20/0.53    inference(negated_conjecture,[],[f15])).
% 1.20/0.53  fof(f15,conjecture,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f42,f40])).
% 1.20/0.53  fof(f40,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.20/0.53  fof(f42,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f20])).
% 1.20/0.53  fof(f20,plain,(
% 1.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f11])).
% 1.20/0.53  fof(f11,axiom,(
% 1.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.20/0.53  fof(f73,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.20/0.53    inference(resolution,[],[f44,f39])).
% 1.20/0.53  fof(f39,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.20/0.53  fof(f44,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f27])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(nnf_transformation,[],[f3])).
% 1.20/0.53  fof(f3,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.20/0.53  fof(f180,plain,(
% 1.20/0.53    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(k3_subset_1(sK0,sK2),X2) | k1_xboole_0 = k3_xboole_0(sK1,X2)) )),
% 1.20/0.53    inference(resolution,[],[f160,f45])).
% 1.20/0.53  fof(f45,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f27])).
% 1.20/0.53  fof(f160,plain,(
% 1.20/0.53    ( ! [X1] : (~r1_xboole_0(k3_subset_1(sK0,sK2),X1) | k1_xboole_0 = k3_xboole_0(sK1,X1)) )),
% 1.20/0.53    inference(resolution,[],[f98,f30])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.20/0.53    inference(cnf_transformation,[],[f26])).
% 1.20/0.53  fof(f98,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X2,X1)) )),
% 1.20/0.53    inference(resolution,[],[f46,f44])).
% 1.20/0.53  fof(f46,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f24,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.20/0.53    inference(flattening,[],[f23])).
% 1.20/0.53  fof(f23,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f8])).
% 1.20/0.53  fof(f8,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.20/0.53  fof(f58,plain,(
% 1.20/0.53    sK1 = k3_xboole_0(sK1,sK2)),
% 1.20/0.53    inference(resolution,[],[f41,f29])).
% 1.20/0.53  fof(f29,plain,(
% 1.20/0.53    r1_tarski(sK1,sK2)),
% 1.20/0.53    inference(cnf_transformation,[],[f26])).
% 1.20/0.53  fof(f31,plain,(
% 1.20/0.53    k1_xboole_0 != sK1),
% 1.20/0.53    inference(cnf_transformation,[],[f26])).
% 1.20/0.53  fof(f270,plain,(
% 1.20/0.53    spl3_1),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f269])).
% 1.20/0.53  fof(f269,plain,(
% 1.20/0.53    $false | spl3_1),
% 1.20/0.53    inference(resolution,[],[f263,f32])).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f7])).
% 1.20/0.53  fof(f7,axiom,(
% 1.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.20/0.53  fof(f263,plain,(
% 1.20/0.53    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2)) | spl3_1),
% 1.20/0.53    inference(avatar_component_clause,[],[f261])).
% 1.20/0.53  fof(f261,plain,(
% 1.20/0.53    spl3_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.20/0.53  fof(f268,plain,(
% 1.20/0.53    ~spl3_1 | spl3_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f259,f265,f261])).
% 1.20/0.53  fof(f259,plain,(
% 1.20/0.53    r1_tarski(sK2,sK0) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2))),
% 1.20/0.53    inference(forward_demodulation,[],[f258,f48])).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.20/0.53    inference(definition_unfolding,[],[f34,f47])).
% 1.20/0.53  fof(f47,plain,(
% 1.20/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f36,f33])).
% 1.20/0.53  fof(f33,plain,(
% 1.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f9])).
% 1.20/0.53  fof(f9,axiom,(
% 1.20/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.20/0.53  fof(f36,plain,(
% 1.20/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f12])).
% 1.20/0.53  fof(f12,axiom,(
% 1.20/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f10])).
% 1.20/0.53  fof(f10,axiom,(
% 1.20/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.20/0.53  fof(f258,plain,(
% 1.20/0.53    r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2))),
% 1.20/0.53    inference(resolution,[],[f200,f35])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f14])).
% 1.20/0.53  fof(f14,axiom,(
% 1.20/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.20/0.53  fof(f200,plain,(
% 1.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_subset_1(sK0,X0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK2))) )),
% 1.20/0.53    inference(resolution,[],[f43,f28])).
% 1.20/0.53  fof(f43,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f22])).
% 1.20/0.53  fof(f22,plain,(
% 1.20/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(flattening,[],[f21])).
% 1.20/0.53  fof(f21,plain,(
% 1.20/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f13])).
% 1.20/0.53  fof(f13,axiom,(
% 1.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (12132)------------------------------
% 1.20/0.53  % (12132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (12132)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (12132)Memory used [KB]: 6268
% 1.20/0.53  % (12132)Time elapsed: 0.124 s
% 1.20/0.53  % (12132)------------------------------
% 1.20/0.53  % (12132)------------------------------
% 1.20/0.53  % (12135)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.53  % (12147)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.20/0.53  % (12135)Refutation not found, incomplete strategy% (12135)------------------------------
% 1.20/0.53  % (12135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (12135)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (12135)Memory used [KB]: 6140
% 1.20/0.53  % (12135)Time elapsed: 0.002 s
% 1.20/0.53  % (12135)------------------------------
% 1.20/0.53  % (12135)------------------------------
% 1.20/0.53  % (12122)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.53  % (12119)Success in time 0.163 s
%------------------------------------------------------------------------------
