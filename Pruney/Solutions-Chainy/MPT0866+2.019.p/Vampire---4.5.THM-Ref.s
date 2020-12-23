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
% DateTime   : Thu Dec  3 12:58:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 197 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  163 ( 561 expanded)
%              Number of equality atoms :   54 ( 258 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f56,f214])).

fof(f214,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f212,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f212,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(resolution,[],[f194,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f194,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f181,f68])).

fof(f68,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f67,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f64,f26])).

% (5326)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f64,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(superposition,[],[f32,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f181,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f143,f165])).

% (5343)Refutation not found, incomplete strategy% (5343)------------------------------
% (5343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5343)Termination reason: Refutation not found, incomplete strategy

% (5343)Memory used [KB]: 10490
% (5343)Time elapsed: 0.092 s
% (5343)------------------------------
% (5343)------------------------------
fof(f165,plain,
    ( ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)
    | ~ spl3_1 ),
    inference(resolution,[],[f161,f36])).

fof(f161,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f150,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))
        | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f143,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f143,plain,
    ( ! [X0] : v1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl3_1 ),
    inference(resolution,[],[f142,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f141,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f59,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f27,f57])).

fof(f27,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f60,f35])).

fof(f60,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f53,f57])).

fof(f53,plain,(
    ! [X0,X1] : ~ r2_hidden(sK2,k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( sK2 != sK2
      | ~ r2_hidden(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f28,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f39,f45,f41])).

fof(f39,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f27,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:48:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (5338)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.43  % (5338)Refutation not found, incomplete strategy% (5338)------------------------------
% 0.20/0.43  % (5338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (5338)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (5338)Memory used [KB]: 6140
% 0.20/0.43  % (5338)Time elapsed: 0.035 s
% 0.20/0.43  % (5338)------------------------------
% 0.20/0.43  % (5338)------------------------------
% 0.20/0.43  % (5329)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (5335)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.45  % (5335)Refutation not found, incomplete strategy% (5335)------------------------------
% 0.20/0.45  % (5335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (5335)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (5335)Memory used [KB]: 1535
% 0.20/0.45  % (5335)Time elapsed: 0.052 s
% 0.20/0.45  % (5335)------------------------------
% 0.20/0.45  % (5335)------------------------------
% 0.20/0.46  % (5327)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (5322)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (5323)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (5340)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % (5325)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (5322)Refutation not found, incomplete strategy% (5322)------------------------------
% 0.20/0.47  % (5322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5322)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5322)Memory used [KB]: 6140
% 0.20/0.47  % (5322)Time elapsed: 0.071 s
% 0.20/0.47  % (5322)------------------------------
% 0.20/0.47  % (5322)------------------------------
% 0.20/0.47  % (5323)Refutation not found, incomplete strategy% (5323)------------------------------
% 0.20/0.47  % (5323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5323)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5323)Memory used [KB]: 10490
% 0.20/0.47  % (5323)Time elapsed: 0.072 s
% 0.20/0.47  % (5323)------------------------------
% 0.20/0.47  % (5323)------------------------------
% 0.20/0.47  % (5342)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.47  % (5343)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (5330)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (5331)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (5342)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f48,f56,f214])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f213])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    $false | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f212,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    k1_xboole_0 != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f194,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    v1_xboole_0(sK1) | ~spl3_1),
% 0.20/0.47    inference(forward_demodulation,[],[f181,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    sK1 = k2_relat_1(k1_xboole_0) | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f67,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    sK1 = k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK0 | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f26])).
% 0.20/0.47  % (5326)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    sK1 = k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_1),
% 0.20/0.47    inference(superposition,[],[f32,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f43,f36])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl3_1 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl3_1),
% 0.20/0.47    inference(backward_demodulation,[],[f143,f165])).
% 0.20/0.47  % (5343)Refutation not found, incomplete strategy% (5343)------------------------------
% 0.20/0.47  % (5343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5343)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5343)Memory used [KB]: 10490
% 0.20/0.47  % (5343)Time elapsed: 0.092 s
% 0.20/0.47  % (5343)------------------------------
% 0.20/0.47  % (5343)------------------------------
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)) ) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f161,f36])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f150,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f143,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ( ! [X0] : (v1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f142,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f141,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK2,X0) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl3_1),
% 0.20/0.47    inference(superposition,[],[f59,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_xboole_0) | ~spl3_1),
% 0.20/0.47    inference(backward_demodulation,[],[f27,f57])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,X0)) ) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f87,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK2,X0) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl3_1),
% 0.20/0.47    inference(superposition,[],[f60,f35])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~r2_hidden(sK2,k1_xboole_0) | ~spl3_1),
% 0.20/0.47    inference(superposition,[],[f53,f57])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK2,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(resolution,[],[f52,f34])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~r2_hidden(sK2,X0)) )),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (sK2 != sK2 | ~r2_hidden(sK2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(superposition,[],[f28,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ~spl3_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    $false | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f53,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl3_2 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl3_1 | spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f45,f41])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    inference(resolution,[],[f27,f30])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (5342)------------------------------
% 0.20/0.48  % (5342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5342)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (5342)Memory used [KB]: 6140
% 0.20/0.48  % (5342)Time elapsed: 0.079 s
% 0.20/0.48  % (5342)------------------------------
% 0.20/0.48  % (5342)------------------------------
% 0.20/0.48  % (5325)Refutation not found, incomplete strategy% (5325)------------------------------
% 0.20/0.48  % (5325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5325)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (5325)Memory used [KB]: 10618
% 0.20/0.48  % (5325)Time elapsed: 0.076 s
% 0.20/0.48  % (5325)------------------------------
% 0.20/0.48  % (5325)------------------------------
% 0.20/0.48  % (5320)Success in time 0.13 s
%------------------------------------------------------------------------------
