%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 178 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  275 ( 574 expanded)
%              Number of equality atoms :   49 (  64 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f423,f572])).

fof(f572,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f568,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f74,f73])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f74,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f568,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | spl3_1 ),
    inference(resolution,[],[f562,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f86,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_tarski(X3,X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f65,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f562,plain,
    ( ! [X0] : r1_tarski(k1_tarski(sK1),X0)
    | spl3_1 ),
    inference(resolution,[],[f559,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f559,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tarski(sK1))
        | r1_tarski(X0,X1) )
    | spl3_1 ),
    inference(resolution,[],[f556,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f556,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_tarski(sK1)))
        | r1_tarski(X4,X5) )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f555,f429])).

fof(f429,plain,
    ( sK0 != k1_tarski(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f428,f45])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

% (24457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (24460)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (24471)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (24463)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (24465)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (24469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (24476)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (24474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (24449)Refutation not found, incomplete strategy% (24449)------------------------------
% (24449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24449)Termination reason: Refutation not found, incomplete strategy

% (24449)Memory used [KB]: 10746
% (24449)Time elapsed: 0.126 s
% (24449)------------------------------
% (24449)------------------------------
% (24452)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (24477)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% (24457)Refutation not found, incomplete strategy% (24457)------------------------------
% (24457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24457)Termination reason: Refutation not found, incomplete strategy

% (24457)Memory used [KB]: 10618
% (24457)Time elapsed: 0.150 s
% (24457)------------------------------
% (24457)------------------------------
fof(f37,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f428,plain,
    ( sK0 != k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f427,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f427,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | spl3_1 ),
    inference(superposition,[],[f117,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f117,plain,
    ( sK0 != k6_domain_1(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_1
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f555,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_tarski(sK1)))
      | sK0 = k1_tarski(sK1) ) ),
    inference(resolution,[],[f160,f46])).

fof(f160,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,sK0)
      | r1_tarski(X10,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k1_tarski(X9)))
      | sK0 = k1_tarski(X9) ) ),
    inference(resolution,[],[f156,f107])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f102,f61])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(sK0,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f156,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
      | sK0 = X6
      | r1_tarski(X5,X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f152,f69])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f151,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK0 = X0 ) ),
    inference(resolution,[],[f149,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f149,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | sK0 = X0
      | ~ r1_tarski(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f423,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f421,f52])).

fof(f52,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f421,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f420,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f420,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f413,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f81,f53])).

fof(f53,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f79,f53])).

fof(f79,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f78,f52])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f58,f56])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f413,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f47,f118])).

fof(f118,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f47,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (24448)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.48  % (24456)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.48  % (24456)Refutation not found, incomplete strategy% (24456)------------------------------
% 0.20/0.48  % (24456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24456)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (24456)Memory used [KB]: 10746
% 0.20/0.48  % (24456)Time elapsed: 0.057 s
% 0.20/0.48  % (24456)------------------------------
% 0.20/0.48  % (24456)------------------------------
% 0.20/0.50  % (24470)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (24450)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (24462)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (24455)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (24468)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (24449)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (24447)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (24447)Refutation not found, incomplete strategy% (24447)------------------------------
% 0.20/0.53  % (24447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24447)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24447)Memory used [KB]: 1663
% 0.20/0.53  % (24447)Time elapsed: 0.126 s
% 0.20/0.53  % (24447)------------------------------
% 0.20/0.53  % (24447)------------------------------
% 0.20/0.53  % (24454)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (24451)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (24450)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f573,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f423,f572])).
% 0.20/0.54  fof(f572,plain,(
% 0.20/0.54    spl3_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f571])).
% 0.20/0.54  fof(f571,plain,(
% 0.20/0.54    $false | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f568,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.20/0.54    inference(superposition,[],[f74,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f50,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f59,f60])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.54  fof(f568,plain,(
% 0.20/0.54    k1_xboole_0 = k1_tarski(sK1) | spl3_1),
% 0.20/0.54    inference(resolution,[],[f562,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f86,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r1_tarski(X3,X4) | X3 = X4) )),
% 0.20/0.54    inference(resolution,[],[f65,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f562,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_tarski(sK1),X0)) ) | spl3_1),
% 0.20/0.54    inference(resolution,[],[f559,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f559,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(sK1)) | r1_tarski(X0,X1)) ) | spl3_1),
% 0.20/0.54    inference(resolution,[],[f556,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f556,plain,(
% 0.20/0.54    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k1_tarski(sK1))) | r1_tarski(X4,X5)) ) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f555,f429])).
% 0.20/0.54  fof(f429,plain,(
% 0.20/0.54    sK0 != k1_tarski(sK1) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f428,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ~v1_xboole_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  % (24457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (24460)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (24471)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (24463)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (24465)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (24469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (24476)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (24474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (24449)Refutation not found, incomplete strategy% (24449)------------------------------
% 0.20/0.55  % (24449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24449)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (24449)Memory used [KB]: 10746
% 0.20/0.55  % (24449)Time elapsed: 0.126 s
% 0.20/0.55  % (24449)------------------------------
% 0.20/0.55  % (24449)------------------------------
% 0.20/0.56  % (24452)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (24477)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.56  % (24457)Refutation not found, incomplete strategy% (24457)------------------------------
% 0.20/0.56  % (24457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (24457)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (24457)Memory used [KB]: 10618
% 0.20/0.56  % (24457)Time elapsed: 0.150 s
% 0.20/0.56  % (24457)------------------------------
% 0.20/0.56  % (24457)------------------------------
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f36,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.56    inference(negated_conjecture,[],[f18])).
% 0.20/0.56  fof(f18,conjecture,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.56  fof(f428,plain,(
% 0.20/0.56    sK0 != k1_tarski(sK1) | v1_xboole_0(sK0) | spl3_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f427,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    m1_subset_1(sK1,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f427,plain,(
% 0.20/0.56    sK0 != k1_tarski(sK1) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | spl3_1),
% 0.20/0.56    inference(superposition,[],[f117,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.56  fof(f117,plain,(
% 0.20/0.56    sK0 != k6_domain_1(sK0,sK1) | spl3_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f116])).
% 0.20/0.56  fof(f116,plain,(
% 0.20/0.56    spl3_1 <=> sK0 = k6_domain_1(sK0,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.56  fof(f555,plain,(
% 0.20/0.56    ( ! [X4,X5] : (r1_tarski(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k1_tarski(sK1))) | sK0 = k1_tarski(sK1)) )),
% 0.20/0.56    inference(resolution,[],[f160,f46])).
% 0.20/0.56  fof(f160,plain,(
% 0.20/0.56    ( ! [X10,X11,X9] : (~m1_subset_1(X9,sK0) | r1_tarski(X10,X11) | ~m1_subset_1(X10,k1_zfmisc_1(k1_tarski(X9))) | sK0 = k1_tarski(X9)) )),
% 0.20/0.56    inference(resolution,[],[f156,f107])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f106,f45])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.20/0.56    inference(superposition,[],[f102,f61])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k6_domain_1(sK0,X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,sK0)) )),
% 0.20/0.56    inference(resolution,[],[f62,f45])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    ( ! [X6,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(sK0)) | sK0 = X6 | r1_tarski(X5,X7) | ~m1_subset_1(X5,k1_zfmisc_1(X6))) )),
% 0.20/0.56    inference(resolution,[],[f152,f69])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK0 = X0 | r1_tarski(X1,X2)) )),
% 0.20/0.56    inference(resolution,[],[f151,f67])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_tarski(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK0 = X0) )),
% 0.20/0.56    inference(resolution,[],[f149,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    ( ! [X0] : (v1_xboole_0(X0) | sK0 = X0 | ~r1_tarski(X0,sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f148,f45])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(resolution,[],[f55,f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    v1_zfmisc_1(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,axiom,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.56  fof(f423,plain,(
% 0.20/0.56    ~spl3_1),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f422])).
% 0.20/0.56  fof(f422,plain,(
% 0.20/0.56    $false | ~spl3_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f421,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.56  fof(f421,plain,(
% 0.20/0.56    ~l1_orders_2(k2_yellow_1(sK0)) | ~spl3_1),
% 0.20/0.56    inference(resolution,[],[f420,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.56  fof(f420,plain,(
% 0.20/0.56    ~l1_struct_0(k2_yellow_1(sK0)) | ~spl3_1),
% 0.20/0.56    inference(resolution,[],[f413,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_subset_1(X0,X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f81,f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_subset_1(X0,u1_struct_0(k2_yellow_1(X0))) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(superposition,[],[f57,f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.56    inference(forward_demodulation,[],[f79,f53])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(resolution,[],[f78,f52])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.56    inference(resolution,[],[f58,f56])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.20/0.56  fof(f413,plain,(
% 0.20/0.56    v1_subset_1(sK0,sK0) | ~spl3_1),
% 0.20/0.56    inference(backward_demodulation,[],[f47,f118])).
% 0.20/0.56  fof(f118,plain,(
% 0.20/0.56    sK0 = k6_domain_1(sK0,sK1) | ~spl3_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f116])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (24450)------------------------------
% 0.20/0.56  % (24450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (24450)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (24450)Memory used [KB]: 11001
% 0.20/0.56  % (24450)Time elapsed: 0.115 s
% 0.20/0.56  % (24450)------------------------------
% 0.20/0.56  % (24450)------------------------------
% 0.20/0.56  % (24446)Success in time 0.203 s
%------------------------------------------------------------------------------
