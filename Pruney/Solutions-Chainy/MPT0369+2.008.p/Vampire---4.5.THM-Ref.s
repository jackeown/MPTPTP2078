%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:24 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  187 ( 453 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f148,f178])).

fof(f178,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f59,f175])).

fof(f175,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(global_subsumption,[],[f33,f173])).

fof(f173,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f172,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f172,plain,(
    ~ r2_hidden(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f34,f170])).

fof(f170,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f67,f156])).

fof(f156,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f90,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f90,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f82,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK0),sK1)
      | r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
          & ~ r2_hidden(X2,sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f67,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f31,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f34,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f148,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f146,f58,f55])).

fof(f55,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f146,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f30,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f56,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (10977)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (10970)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (10984)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (10992)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (10977)Refutation not found, incomplete strategy% (10977)------------------------------
% 0.21/0.56  % (10977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10967)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (10968)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (10977)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10977)Memory used [KB]: 10618
% 0.21/0.57  % (10977)Time elapsed: 0.136 s
% 0.21/0.57  % (10977)------------------------------
% 0.21/0.57  % (10977)------------------------------
% 0.21/0.57  % (10966)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.57  % (10981)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.57  % (10975)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.58  % (10979)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.58  % (10972)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.58  % (10969)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.58  % (10987)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.59  % (10978)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.59  % (10989)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.59  % (10995)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.59  % (10968)Refutation found. Thanks to Tanya!
% 1.56/0.59  % SZS status Theorem for theBenchmark
% 1.56/0.59  % SZS output start Proof for theBenchmark
% 1.56/0.59  fof(f179,plain,(
% 1.56/0.59    $false),
% 1.56/0.59    inference(avatar_sat_refutation,[],[f117,f148,f178])).
% 1.56/0.59  fof(f178,plain,(
% 1.56/0.59    ~spl4_2),
% 1.56/0.59    inference(avatar_contradiction_clause,[],[f176])).
% 1.56/0.59  fof(f176,plain,(
% 1.56/0.59    $false | ~spl4_2),
% 1.56/0.59    inference(subsumption_resolution,[],[f59,f175])).
% 1.56/0.59  fof(f175,plain,(
% 1.56/0.59    ~r2_hidden(sK2,sK0)),
% 1.56/0.59    inference(global_subsumption,[],[f33,f173])).
% 1.56/0.59  fof(f173,plain,(
% 1.56/0.59    r2_hidden(sK2,sK1) | ~r2_hidden(sK2,sK0)),
% 1.56/0.59    inference(resolution,[],[f172,f49])).
% 1.56/0.59  fof(f49,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f29])).
% 1.56/0.59  fof(f29,plain,(
% 1.56/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.56/0.59    inference(nnf_transformation,[],[f21])).
% 1.56/0.59  fof(f21,plain,(
% 1.56/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.56/0.59    inference(ennf_transformation,[],[f4])).
% 1.56/0.59  fof(f4,axiom,(
% 1.56/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.56/0.59  fof(f172,plain,(
% 1.56/0.59    ~r2_hidden(sK2,k5_xboole_0(sK0,sK1))),
% 1.56/0.59    inference(backward_demodulation,[],[f34,f170])).
% 1.56/0.59  fof(f170,plain,(
% 1.56/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.56/0.59    inference(backward_demodulation,[],[f67,f156])).
% 1.56/0.59  fof(f156,plain,(
% 1.56/0.59    sK1 = k3_xboole_0(sK0,sK1)),
% 1.56/0.59    inference(superposition,[],[f90,f36])).
% 1.56/0.59  fof(f36,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f1])).
% 1.56/0.59  fof(f1,axiom,(
% 1.56/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.59  fof(f90,plain,(
% 1.56/0.59    sK1 = k3_xboole_0(sK1,sK0)),
% 1.56/0.59    inference(resolution,[],[f84,f42])).
% 1.56/0.59  fof(f42,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.56/0.59    inference(cnf_transformation,[],[f17])).
% 1.56/0.59  fof(f17,plain,(
% 1.56/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.56/0.59    inference(ennf_transformation,[],[f6])).
% 1.56/0.59  fof(f6,axiom,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.56/0.59  fof(f84,plain,(
% 1.56/0.59    r1_tarski(sK1,sK0)),
% 1.56/0.59    inference(duplicate_literal_removal,[],[f83])).
% 1.56/0.59  fof(f83,plain,(
% 1.56/0.59    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.56/0.59    inference(resolution,[],[f82,f45])).
% 1.56/0.59  fof(f45,plain,(
% 1.56/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f28])).
% 1.56/0.59  fof(f28,plain,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).
% 1.56/0.59  fof(f27,plain,(
% 1.56/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f20,plain,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f12])).
% 1.56/0.59  fof(f12,plain,(
% 1.56/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.56/0.59    inference(unused_predicate_definition_removal,[],[f2])).
% 1.56/0.59  fof(f2,axiom,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.59  fof(f82,plain,(
% 1.56/0.59    ( ! [X0] : (~r2_hidden(sK3(X0,sK0),sK1) | r1_tarski(X0,sK0)) )),
% 1.56/0.59    inference(resolution,[],[f66,f46])).
% 1.56/0.59  fof(f46,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f28])).
% 1.56/0.59  fof(f66,plain,(
% 1.56/0.59    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) )),
% 1.56/0.59    inference(resolution,[],[f31,f44])).
% 1.56/0.59  fof(f44,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f19])).
% 1.56/0.59  fof(f19,plain,(
% 1.56/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f9])).
% 1.56/0.59  fof(f9,axiom,(
% 1.56/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.56/0.59  fof(f31,plain,(
% 1.56/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.59    inference(cnf_transformation,[],[f25])).
% 1.56/0.59  fof(f25,plain,(
% 1.56/0.59    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24,f23,f22])).
% 1.56/0.59  fof(f22,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f23,plain,(
% 1.56/0.59    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f24,plain,(
% 1.56/0.59    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f14,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.56/0.59    inference(flattening,[],[f13])).
% 1.56/0.59  fof(f13,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.56/0.59    inference(ennf_transformation,[],[f11])).
% 1.56/0.59  fof(f11,negated_conjecture,(
% 1.56/0.59    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.56/0.59    inference(negated_conjecture,[],[f10])).
% 1.56/0.59  fof(f10,conjecture,(
% 1.56/0.59    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.56/0.59  fof(f67,plain,(
% 1.56/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.56/0.59    inference(resolution,[],[f31,f51])).
% 1.56/0.59  fof(f51,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f43,f37])).
% 1.56/0.59  fof(f37,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.56/0.59    inference(cnf_transformation,[],[f5])).
% 1.56/0.59  fof(f5,axiom,(
% 1.56/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.56/0.59  fof(f43,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.56/0.59    inference(cnf_transformation,[],[f18])).
% 1.56/0.59  fof(f18,plain,(
% 1.56/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f8])).
% 1.56/0.59  fof(f8,axiom,(
% 1.56/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.56/0.59  fof(f34,plain,(
% 1.56/0.59    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.56/0.59    inference(cnf_transformation,[],[f25])).
% 1.56/0.59  fof(f33,plain,(
% 1.56/0.59    ~r2_hidden(sK2,sK1)),
% 1.56/0.59    inference(cnf_transformation,[],[f25])).
% 1.56/0.59  fof(f59,plain,(
% 1.56/0.59    r2_hidden(sK2,sK0) | ~spl4_2),
% 1.56/0.59    inference(avatar_component_clause,[],[f58])).
% 1.56/0.59  fof(f58,plain,(
% 1.56/0.59    spl4_2 <=> r2_hidden(sK2,sK0)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.56/0.59  fof(f148,plain,(
% 1.56/0.59    spl4_1 | spl4_2),
% 1.56/0.59    inference(avatar_split_clause,[],[f146,f58,f55])).
% 1.56/0.59  fof(f55,plain,(
% 1.56/0.59    spl4_1 <=> v1_xboole_0(sK0)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.56/0.59  fof(f146,plain,(
% 1.56/0.59    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 1.56/0.59    inference(resolution,[],[f32,f38])).
% 1.56/0.59  fof(f38,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f26])).
% 1.56/0.59  fof(f26,plain,(
% 1.56/0.59    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.56/0.59    inference(nnf_transformation,[],[f16])).
% 1.56/0.59  fof(f16,plain,(
% 1.56/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f7])).
% 1.56/0.59  fof(f7,axiom,(
% 1.56/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.56/0.59  fof(f32,plain,(
% 1.56/0.59    m1_subset_1(sK2,sK0)),
% 1.56/0.59    inference(cnf_transformation,[],[f25])).
% 1.56/0.59  fof(f117,plain,(
% 1.56/0.59    ~spl4_1),
% 1.56/0.59    inference(avatar_contradiction_clause,[],[f103])).
% 1.56/0.59  fof(f103,plain,(
% 1.56/0.59    $false | ~spl4_1),
% 1.56/0.59    inference(subsumption_resolution,[],[f30,f101])).
% 1.56/0.59  fof(f101,plain,(
% 1.56/0.59    k1_xboole_0 = sK0 | ~spl4_1),
% 1.56/0.59    inference(resolution,[],[f56,f35])).
% 1.56/0.59  fof(f35,plain,(
% 1.56/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.56/0.59    inference(cnf_transformation,[],[f15])).
% 1.56/0.59  fof(f15,plain,(
% 1.56/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.56/0.59    inference(ennf_transformation,[],[f3])).
% 1.56/0.59  fof(f3,axiom,(
% 1.56/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.56/0.59  fof(f56,plain,(
% 1.56/0.59    v1_xboole_0(sK0) | ~spl4_1),
% 1.56/0.59    inference(avatar_component_clause,[],[f55])).
% 1.56/0.59  fof(f30,plain,(
% 1.56/0.59    k1_xboole_0 != sK0),
% 1.56/0.59    inference(cnf_transformation,[],[f25])).
% 1.56/0.59  % SZS output end Proof for theBenchmark
% 1.56/0.59  % (10968)------------------------------
% 1.56/0.59  % (10968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (10968)Termination reason: Refutation
% 1.56/0.59  
% 1.56/0.59  % (10968)Memory used [KB]: 10746
% 1.56/0.59  % (10968)Time elapsed: 0.167 s
% 1.56/0.59  % (10968)------------------------------
% 1.56/0.59  % (10968)------------------------------
% 1.56/0.60  % (10994)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.80/0.60  % (10965)Success in time 0.23 s
%------------------------------------------------------------------------------
