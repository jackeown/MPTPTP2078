%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 128 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   17
%              Number of atoms          :  226 ( 350 expanded)
%              Number of equality atoms :   49 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f93,f191,f197,f280])).

fof(f280,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f275,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).

% (4303)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (4304)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (4298)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (4326)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (4305)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (4327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (4317)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (4322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (4318)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f27,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(f275,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f237,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f237,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0 )
    | ~ spl3_3 ),
    inference(resolution,[],[f236,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f236,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl3_3 ),
    inference(resolution,[],[f229,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f229,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f210,f39])).

fof(f210,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,X2))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f110,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f110,plain,(
    ! [X2] :
      ( ~ r1_tarski(k7_setfam_1(sK0,sK1),k3_subset_1(sK0,X2))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f57,f60])).

fof(f60,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f36,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f197,plain,
    ( ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f195,f38])).

fof(f38,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f195,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f194,f92])).

fof(f92,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_4
  <=> k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f194,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))))
    | ~ spl3_11 ),
    inference(resolution,[],[f140,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f140,plain,
    ( m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_11
  <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f191,plain,
    ( ~ spl3_1
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl3_1
    | spl3_11 ),
    inference(subsumption_resolution,[],[f188,f67])).

fof(f67,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_1
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f188,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_11 ),
    inference(resolution,[],[f141,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f141,plain,
    ( ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f93,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f84,f66,f90,f86])).

fof(f84,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f79,f59])).

fof(f59,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f79,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

fof(f77,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f75,f36])).

fof(f75,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1 ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f68,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:54:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (4300)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (4301)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (4308)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (4320)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (4316)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (4320)Refutation not found, incomplete strategy% (4320)------------------------------
% 0.22/0.57  % (4320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4320)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (4320)Memory used [KB]: 10618
% 0.22/0.57  % (4320)Time elapsed: 0.129 s
% 0.22/0.57  % (4320)------------------------------
% 0.22/0.57  % (4320)------------------------------
% 0.22/0.57  % (4309)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (4308)Refutation not found, incomplete strategy% (4308)------------------------------
% 0.22/0.58  % (4308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (4302)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (4313)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (4306)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.59  % (4321)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (4308)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (4308)Memory used [KB]: 10874
% 0.22/0.59  % (4308)Time elapsed: 0.139 s
% 0.22/0.59  % (4308)------------------------------
% 0.22/0.59  % (4308)------------------------------
% 0.22/0.59  % (4306)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f281,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f77,f93,f191,f197,f280])).
% 0.22/0.59  fof(f280,plain,(
% 0.22/0.59    ~spl3_3),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.59  fof(f279,plain,(
% 0.22/0.59    $false | ~spl3_3),
% 0.22/0.59    inference(subsumption_resolution,[],[f275,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    k1_xboole_0 != sK1),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).
% 1.56/0.60  % (4303)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.60  % (4304)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.61  % (4298)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.61  % (4326)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.61  % (4305)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.61  % (4327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.61  % (4317)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.61  % (4322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.61  % (4318)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.62  fof(f27,plain,(
% 1.56/0.62    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.56/0.62    introduced(choice_axiom,[])).
% 1.56/0.62  fof(f15,plain,(
% 1.56/0.62    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(flattening,[],[f14])).
% 1.56/0.62  fof(f14,plain,(
% 1.56/0.62    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(ennf_transformation,[],[f13])).
% 1.56/0.62  fof(f13,negated_conjecture,(
% 1.56/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 1.56/0.62    inference(negated_conjecture,[],[f12])).
% 1.56/0.62  fof(f12,conjecture,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).
% 1.56/0.62  fof(f275,plain,(
% 1.56/0.62    k1_xboole_0 = sK1 | ~spl3_3),
% 1.56/0.62    inference(resolution,[],[f237,f39])).
% 1.56/0.62  fof(f39,plain,(
% 1.56/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f3])).
% 1.56/0.62  fof(f3,axiom,(
% 1.56/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.56/0.62  fof(f237,plain,(
% 1.56/0.62    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0) ) | ~spl3_3),
% 1.56/0.62    inference(resolution,[],[f236,f49])).
% 1.56/0.62  fof(f49,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f31])).
% 1.56/0.62  fof(f31,plain,(
% 1.56/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.62    inference(flattening,[],[f30])).
% 1.56/0.62  fof(f30,plain,(
% 1.56/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.62    inference(nnf_transformation,[],[f2])).
% 1.56/0.62  fof(f2,axiom,(
% 1.56/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.62  fof(f236,plain,(
% 1.56/0.62    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl3_3),
% 1.56/0.62    inference(resolution,[],[f229,f51])).
% 1.56/0.62  fof(f51,plain,(
% 1.56/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f35])).
% 1.56/0.62  fof(f35,plain,(
% 1.56/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.56/0.62  fof(f34,plain,(
% 1.56/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.56/0.62    introduced(choice_axiom,[])).
% 1.56/0.62  fof(f33,plain,(
% 1.56/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.62    inference(rectify,[],[f32])).
% 1.56/0.62  fof(f32,plain,(
% 1.56/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.62    inference(nnf_transformation,[],[f23])).
% 1.56/0.62  fof(f23,plain,(
% 1.56/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.62    inference(ennf_transformation,[],[f1])).
% 1.56/0.62  fof(f1,axiom,(
% 1.56/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.62  fof(f229,plain,(
% 1.56/0.62    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl3_3),
% 1.56/0.62    inference(subsumption_resolution,[],[f210,f39])).
% 1.56/0.62  fof(f210,plain,(
% 1.56/0.62    ( ! [X2] : (~r1_tarski(k1_xboole_0,k3_subset_1(sK0,X2)) | ~r2_hidden(X2,sK1)) ) | ~spl3_3),
% 1.56/0.62    inference(backward_demodulation,[],[f110,f88])).
% 1.56/0.62  fof(f88,plain,(
% 1.56/0.62    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_3),
% 1.56/0.62    inference(avatar_component_clause,[],[f86])).
% 1.56/0.62  fof(f86,plain,(
% 1.56/0.62    spl3_3 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.56/0.62  fof(f110,plain,(
% 1.56/0.62    ( ! [X2] : (~r1_tarski(k7_setfam_1(sK0,sK1),k3_subset_1(sK0,X2)) | ~r2_hidden(X2,sK1)) )),
% 1.56/0.62    inference(resolution,[],[f106,f53])).
% 1.56/0.62  fof(f53,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f24])).
% 1.56/0.62  fof(f24,plain,(
% 1.56/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.56/0.62    inference(ennf_transformation,[],[f10])).
% 1.56/0.62  fof(f10,axiom,(
% 1.56/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.56/0.62  fof(f106,plain,(
% 1.56/0.62    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 1.56/0.62    inference(duplicate_literal_removal,[],[f104])).
% 1.56/0.62  fof(f104,plain,(
% 1.56/0.62    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 1.56/0.62    inference(resolution,[],[f57,f60])).
% 1.56/0.62  fof(f60,plain,(
% 1.56/0.62    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~r2_hidden(X1,sK1)) )),
% 1.56/0.62    inference(resolution,[],[f36,f54])).
% 1.56/0.62  fof(f54,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f26])).
% 1.56/0.62  fof(f26,plain,(
% 1.56/0.62    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.56/0.62    inference(flattening,[],[f25])).
% 1.56/0.62  fof(f25,plain,(
% 1.56/0.62    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.56/0.62    inference(ennf_transformation,[],[f9])).
% 1.56/0.62  fof(f9,axiom,(
% 1.56/0.62    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.56/0.62  fof(f36,plain,(
% 1.56/0.62    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.56/0.62    inference(cnf_transformation,[],[f28])).
% 1.56/0.62  fof(f57,plain,(
% 1.56/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))) )),
% 1.56/0.62    inference(resolution,[],[f36,f46])).
% 1.56/0.62  fof(f46,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f29])).
% 1.56/0.62  fof(f29,plain,(
% 1.56/0.62    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(nnf_transformation,[],[f22])).
% 1.56/0.62  fof(f22,plain,(
% 1.56/0.62    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(ennf_transformation,[],[f8])).
% 1.56/0.62  fof(f8,axiom,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 1.56/0.62  fof(f197,plain,(
% 1.56/0.62    ~spl3_4 | ~spl3_11),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f196])).
% 1.56/0.62  fof(f196,plain,(
% 1.56/0.62    $false | (~spl3_4 | ~spl3_11)),
% 1.56/0.62    inference(subsumption_resolution,[],[f195,f38])).
% 1.56/0.62  fof(f38,plain,(
% 1.56/0.62    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 1.56/0.62    inference(cnf_transformation,[],[f28])).
% 1.56/0.62  fof(f195,plain,(
% 1.56/0.62    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | (~spl3_4 | ~spl3_11)),
% 1.56/0.62    inference(forward_demodulation,[],[f194,f92])).
% 1.56/0.62  fof(f92,plain,(
% 1.56/0.62    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl3_4),
% 1.56/0.62    inference(avatar_component_clause,[],[f90])).
% 1.56/0.62  fof(f90,plain,(
% 1.56/0.62    spl3_4 <=> k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.56/0.62  fof(f194,plain,(
% 1.56/0.62    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) | ~spl3_11),
% 1.56/0.62    inference(resolution,[],[f140,f40])).
% 1.56/0.62  fof(f40,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.56/0.62    inference(cnf_transformation,[],[f16])).
% 1.56/0.62  fof(f16,plain,(
% 1.56/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.62    inference(ennf_transformation,[],[f4])).
% 1.56/0.62  fof(f4,axiom,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.56/0.62  fof(f140,plain,(
% 1.56/0.62    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl3_11),
% 1.56/0.62    inference(avatar_component_clause,[],[f139])).
% 1.56/0.62  fof(f139,plain,(
% 1.56/0.62    spl3_11 <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.56/0.62  fof(f191,plain,(
% 1.56/0.62    ~spl3_1 | spl3_11),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f190])).
% 1.56/0.62  fof(f190,plain,(
% 1.56/0.62    $false | (~spl3_1 | spl3_11)),
% 1.56/0.62    inference(subsumption_resolution,[],[f188,f67])).
% 1.56/0.62  fof(f67,plain,(
% 1.56/0.62    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_1),
% 1.56/0.62    inference(avatar_component_clause,[],[f66])).
% 1.56/0.62  fof(f66,plain,(
% 1.56/0.62    spl3_1 <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.56/0.62  fof(f188,plain,(
% 1.56/0.62    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_11),
% 1.56/0.62    inference(resolution,[],[f141,f41])).
% 1.56/0.62  fof(f41,plain,(
% 1.56/0.62    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f17])).
% 1.56/0.62  fof(f17,plain,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(ennf_transformation,[],[f5])).
% 1.56/0.62  fof(f5,axiom,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.56/0.62  fof(f141,plain,(
% 1.56/0.62    ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | spl3_11),
% 1.56/0.62    inference(avatar_component_clause,[],[f139])).
% 1.56/0.62  fof(f93,plain,(
% 1.56/0.62    spl3_3 | spl3_4 | ~spl3_1),
% 1.56/0.62    inference(avatar_split_clause,[],[f84,f66,f90,f86])).
% 1.56/0.62  fof(f84,plain,(
% 1.56/0.62    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_1),
% 1.56/0.62    inference(forward_demodulation,[],[f79,f59])).
% 1.56/0.62  fof(f59,plain,(
% 1.56/0.62    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 1.56/0.62    inference(resolution,[],[f36,f42])).
% 1.56/0.62  fof(f42,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 1.56/0.62    inference(cnf_transformation,[],[f18])).
% 1.56/0.62  fof(f18,plain,(
% 1.56/0.62    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(ennf_transformation,[],[f7])).
% 1.56/0.62  fof(f7,axiom,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.56/0.62  fof(f79,plain,(
% 1.56/0.62    k1_xboole_0 = k7_setfam_1(sK0,sK1) | k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl3_1),
% 1.56/0.62    inference(resolution,[],[f67,f44])).
% 1.56/0.62  fof(f44,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f21])).
% 1.56/0.62  fof(f21,plain,(
% 1.56/0.62    ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(flattening,[],[f20])).
% 1.56/0.62  fof(f20,plain,(
% 1.56/0.62    ! [X0,X1] : ((k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(ennf_transformation,[],[f11])).
% 1.56/0.62  fof(f11,axiom,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).
% 1.56/0.62  fof(f77,plain,(
% 1.56/0.62    spl3_1),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f76])).
% 1.56/0.62  fof(f76,plain,(
% 1.56/0.62    $false | spl3_1),
% 1.56/0.62    inference(subsumption_resolution,[],[f75,f36])).
% 1.56/0.62  fof(f75,plain,(
% 1.56/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_1),
% 1.56/0.62    inference(resolution,[],[f68,f43])).
% 1.56/0.62  fof(f43,plain,(
% 1.56/0.62    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f19])).
% 1.56/0.62  fof(f19,plain,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    inference(ennf_transformation,[],[f6])).
% 1.56/0.62  fof(f6,axiom,(
% 1.56/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.56/0.62  fof(f68,plain,(
% 1.56/0.62    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_1),
% 1.56/0.62    inference(avatar_component_clause,[],[f66])).
% 1.56/0.62  % SZS output end Proof for theBenchmark
% 1.56/0.62  % (4306)------------------------------
% 1.56/0.62  % (4306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (4306)Termination reason: Refutation
% 1.56/0.62  
% 1.56/0.62  % (4306)Memory used [KB]: 10746
% 1.56/0.62  % (4306)Time elapsed: 0.157 s
% 1.56/0.62  % (4306)------------------------------
% 1.56/0.62  % (4306)------------------------------
% 1.56/0.62  % (4319)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.62  % (4297)Success in time 0.248 s
%------------------------------------------------------------------------------
