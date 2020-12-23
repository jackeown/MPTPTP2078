%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 172 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  231 ( 643 expanded)
%              Number of equality atoms :    8 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f177,f189,f193,f216,f230,f253,f282])).

fof(f282,plain,
    ( ~ spl6_5
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl6_5
    | spl6_15 ),
    inference(subsumption_resolution,[],[f277,f167])).

fof(f167,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_15
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f277,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f271,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(sK2,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f233,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(sK2,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f69,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f69,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_5
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f253,plain,
    ( ~ spl6_15
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(resolution,[],[f201,f242])).

fof(f242,plain,
    ( ! [X5] : ~ r2_xboole_0(X5,sK1)
    | ~ spl6_20 ),
    inference(resolution,[],[f192,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f192,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_20
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f201,plain,
    ( r2_xboole_0(sK2,sK1)
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f200,f19])).

fof(f19,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f200,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK2,sK1)
    | ~ spl6_15 ),
    inference(resolution,[],[f168,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f168,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f230,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f226,f20])).

fof(f226,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_16 ),
    inference(resolution,[],[f171,f18])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_16
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f216,plain,
    ( ~ spl6_15
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f214,f201])).

fof(f214,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK2,sK1)
    | ~ spl6_17 ),
    inference(resolution,[],[f206,f34])).

fof(f206,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK5(sK2,X6),sK1)
        | ~ r2_xboole_0(sK2,X6) )
    | ~ spl6_17 ),
    inference(resolution,[],[f176,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f176,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK2)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_17
  <=> ! [X1] :
        ( r2_hidden(X1,sK2)
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f193,plain,
    ( ~ spl6_4
    | spl6_20 ),
    inference(avatar_split_clause,[],[f71,f191,f64])).

fof(f64,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f54,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f189,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f188,f68,f64])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(sK0) ) ),
    inference(global_subsumption,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f18,f27])).

fof(f177,plain,
    ( spl6_4
    | spl6_17 ),
    inference(avatar_split_clause,[],[f173,f175,f64])).

fof(f173,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f54])).

fof(f95,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f17,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f17,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f172,plain,
    ( spl6_15
    | spl6_16
    | spl6_4 ),
    inference(avatar_split_clause,[],[f164,f64,f170,f166])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | r1_tarski(sK2,sK1) )
    | spl6_4 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | r1_tarski(sK2,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | r1_tarski(sK2,sK1) )
    | spl6_4 ),
    inference(resolution,[],[f80,f29])).

fof(f80,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK4(X1,X2,sK1),sK2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | r1_tarski(X2,sK1) )
    | spl6_4 ),
    inference(resolution,[],[f78,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK2) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f75,f66])).

fof(f66,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f75,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f16,f25])).

fof(f16,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (10435)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (10427)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (10431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (10430)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (10426)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (10433)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (10425)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (10440)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (10441)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (10429)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (10432)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (10434)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (10426)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f172,f177,f189,f193,f216,f230,f253,f282])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    ~spl6_5 | spl6_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f281])).
% 0.20/0.48  fof(f281,plain,(
% 0.20/0.48    $false | (~spl6_5 | spl6_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f277,f167])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK1) | spl6_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    spl6_15 <=> r1_tarski(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.48  fof(f277,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~spl6_5),
% 0.20/0.48    inference(resolution,[],[f271,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.48  fof(f271,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,X0)) ) | ~spl6_5),
% 0.20/0.48    inference(resolution,[],[f233,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(sK2,X0)) ) | ~spl6_5),
% 0.20/0.48    inference(resolution,[],[f69,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl6_5 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    ~spl6_15 | ~spl6_20),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f252])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    $false | (~spl6_15 | ~spl6_20)),
% 0.20/0.48    inference(resolution,[],[f201,f242])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    ( ! [X5] : (~r2_xboole_0(X5,sK1)) ) | ~spl6_20),
% 0.20/0.48    inference(resolution,[],[f192,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f191])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    spl6_20 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    r2_xboole_0(sK2,sK1) | ~spl6_15),
% 0.20/0.48    inference(subsumption_resolution,[],[f200,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    sK1 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    sK1 = sK2 | r2_xboole_0(sK2,sK1) | ~spl6_15),
% 0.20/0.48    inference(resolution,[],[f168,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~spl6_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f166])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    ~spl6_16),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f229])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    $false | ~spl6_16),
% 0.20/0.48    inference(subsumption_resolution,[],[f226,f20])).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl6_16),
% 0.20/0.48    inference(resolution,[],[f171,f18])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl6_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f170])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    spl6_16 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ~spl6_15 | ~spl6_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f215])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    $false | (~spl6_15 | ~spl6_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f214,f201])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    ~r2_xboole_0(sK2,sK1) | ~spl6_17),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f212])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    ~r2_xboole_0(sK2,sK1) | ~r2_xboole_0(sK2,sK1) | ~spl6_17),
% 0.20/0.48    inference(resolution,[],[f206,f34])).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    ( ! [X6] : (~r2_hidden(sK5(sK2,X6),sK1) | ~r2_xboole_0(sK2,X6)) ) | ~spl6_17),
% 0.20/0.48    inference(resolution,[],[f176,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) ) | ~spl6_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl6_17 <=> ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ~spl6_4 | spl6_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f191,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl6_4 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f54,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f20,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ~spl6_4 | spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f188,f68,f64])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(sK0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f37,f22])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.48    inference(resolution,[],[f18,f27])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    spl6_4 | spl6_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f173,f175,f64])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f54])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0) | v1_xboole_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f17,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    spl6_15 | spl6_16 | spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f164,f64,f170,f166])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,sK1)) ) | spl6_4),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,sK1)) ) | spl6_4),
% 0.20/0.48    inference(resolution,[],[f80,f29])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(sK4(X1,X2,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,sK1)) ) | spl6_4),
% 0.20/0.48    inference(resolution,[],[f78,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK2)) ) | spl6_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f77,f37])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) ) | spl6_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f75,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0) | spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0) | v1_xboole_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f16,f25])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (10426)------------------------------
% 0.20/0.48  % (10426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (10426)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (10426)Memory used [KB]: 10746
% 0.20/0.48  % (10426)Time elapsed: 0.076 s
% 0.20/0.48  % (10426)------------------------------
% 0.20/0.48  % (10426)------------------------------
% 0.20/0.48  % (10424)Success in time 0.134 s
%------------------------------------------------------------------------------
