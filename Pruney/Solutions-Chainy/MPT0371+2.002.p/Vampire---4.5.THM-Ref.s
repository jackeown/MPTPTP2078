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
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 205 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 ( 679 expanded)
%              Number of equality atoms :   15 ( 100 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1387,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1386,f251])).

fof(f251,plain,(
    ~ r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f250,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f99,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f99,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f80,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f80,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f79,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).

fof(f250,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f245,f85])).

fof(f85,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f84,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f84,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f17,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f245,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f207,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | sQ8_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f44,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f207,plain,(
    ~ sQ8_eqProxy(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f130,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sQ8_eqProxy(X0,X1)
      | sQ8_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f130,plain,(
    ~ sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f123,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,
    ( ~ sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f82,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ8_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f30,f58])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ sQ8_eqProxy(X0,k3_subset_1(sK0,sK2))
      | ~ sQ8_eqProxy(sK1,X0) ) ),
    inference(resolution,[],[f60,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ8_eqProxy(X0,X1)
      | ~ sQ8_eqProxy(X1,X2)
      | sQ8_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f60,plain,(
    ~ sQ8_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f20,f58])).

fof(f20,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1386,plain,(
    r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1385,f253])).

fof(f253,plain,(
    ~ r2_hidden(sK7(sK0,sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f247,f251])).

fof(f247,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f207,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | sQ8_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f46,f58])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1385,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f1377])).

fof(f1377,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK2)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1)
    | r2_hidden(sK7(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f180,f207])).

fof(f180,plain,(
    ! [X26,X25] :
      ( sQ8_eqProxy(k4_xboole_0(sK0,X25),X26)
      | r2_hidden(sK7(sK0,X25,X26),sK2)
      | r2_hidden(sK7(sK0,X25,X26),X26)
      | r2_hidden(sK7(sK0,X25,X26),sK1) ) ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | sQ8_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f45,f58])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f88,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f87,f24])).

fof(f87,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f18,f28])).

fof(f18,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (10432)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (10424)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (10414)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (10413)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (10416)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (10409)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (10423)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (10422)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (10412)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (10411)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10410)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (10415)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (10435)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (10438)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (10437)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (10436)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (10434)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (10427)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (10430)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (10425)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (10433)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10429)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (10420)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (10426)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (10419)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (10419)Refutation not found, incomplete strategy% (10419)------------------------------
% 0.22/0.56  % (10419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10419)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10419)Memory used [KB]: 10618
% 0.22/0.56  % (10419)Time elapsed: 0.149 s
% 0.22/0.56  % (10419)------------------------------
% 0.22/0.56  % (10419)------------------------------
% 0.22/0.56  % (10417)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (10428)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (10421)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (10418)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (10431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.93/0.62  % (10422)Refutation found. Thanks to Tanya!
% 1.93/0.62  % SZS status Theorem for theBenchmark
% 1.93/0.62  % SZS output start Proof for theBenchmark
% 2.09/0.64  fof(f1387,plain,(
% 2.09/0.64    $false),
% 2.09/0.64    inference(subsumption_resolution,[],[f1386,f251])).
% 2.09/0.64  fof(f251,plain,(
% 2.09/0.64    ~r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(subsumption_resolution,[],[f250,f116])).
% 2.09/0.64  fof(f116,plain,(
% 2.09/0.64    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 2.09/0.64    inference(resolution,[],[f99,f31])).
% 2.09/0.64  fof(f31,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f16])).
% 2.09/0.64  fof(f16,plain,(
% 2.09/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f2])).
% 2.09/0.64  fof(f2,axiom,(
% 2.09/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.09/0.64  fof(f99,plain,(
% 2.09/0.64    r1_tarski(sK1,sK0)),
% 2.09/0.64    inference(resolution,[],[f80,f50])).
% 2.09/0.64  fof(f50,plain,(
% 2.09/0.64    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(equality_resolution,[],[f35])).
% 2.09/0.64  fof(f35,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.09/0.64    inference(cnf_transformation,[],[f6])).
% 2.09/0.64  fof(f6,axiom,(
% 2.09/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.09/0.64  fof(f80,plain,(
% 2.09/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.09/0.64    inference(subsumption_resolution,[],[f79,f22])).
% 2.09/0.64  fof(f22,plain,(
% 2.09/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f9])).
% 2.09/0.64  fof(f9,axiom,(
% 2.09/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.09/0.64  fof(f79,plain,(
% 2.09/0.64    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.09/0.64    inference(resolution,[],[f21,f29])).
% 2.09/0.64  fof(f29,plain,(
% 2.09/0.64    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f14])).
% 2.09/0.64  fof(f14,plain,(
% 2.09/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f7])).
% 2.09/0.64  fof(f7,axiom,(
% 2.09/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.09/0.64  fof(f21,plain,(
% 2.09/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.09/0.64    inference(cnf_transformation,[],[f13])).
% 2.09/0.64  fof(f13,plain,(
% 2.09/0.64    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(flattening,[],[f12])).
% 2.09/0.64  fof(f12,plain,(
% 2.09/0.64    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f11])).
% 2.09/0.64  fof(f11,negated_conjecture,(
% 2.09/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 2.09/0.64    inference(negated_conjecture,[],[f10])).
% 2.09/0.64  fof(f10,conjecture,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).
% 2.09/0.64  fof(f250,plain,(
% 2.09/0.64    ~r2_hidden(sK7(sK0,sK2,sK1),sK0) | ~r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(subsumption_resolution,[],[f245,f85])).
% 2.09/0.64  fof(f85,plain,(
% 2.09/0.64    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 2.09/0.64    inference(subsumption_resolution,[],[f84,f24])).
% 2.09/0.64  fof(f24,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f1])).
% 2.09/0.64  fof(f1,axiom,(
% 2.09/0.64    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.09/0.64  fof(f84,plain,(
% 2.09/0.64    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 2.09/0.64    inference(resolution,[],[f17,f28])).
% 2.09/0.64  fof(f28,plain,(
% 2.09/0.64    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f14])).
% 2.09/0.64  fof(f17,plain,(
% 2.09/0.64    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f13])).
% 2.09/0.64  fof(f245,plain,(
% 2.09/0.64    ~r2_hidden(sK7(sK0,sK2,sK1),sK0) | r2_hidden(sK7(sK0,sK2,sK1),sK2) | ~r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(resolution,[],[f207,f69])).
% 2.09/0.64  fof(f69,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2) | sQ8_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 2.09/0.64    inference(equality_proxy_replacement,[],[f44,f58])).
% 2.09/0.64  fof(f58,plain,(
% 2.09/0.64    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 2.09/0.64    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 2.09/0.64  fof(f44,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.64    inference(cnf_transformation,[],[f4])).
% 2.09/0.64  fof(f4,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.09/0.64  fof(f207,plain,(
% 2.09/0.64    ~sQ8_eqProxy(k4_xboole_0(sK0,sK2),sK1)),
% 2.09/0.64    inference(resolution,[],[f130,f71])).
% 2.09/0.64  fof(f71,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~sQ8_eqProxy(X0,X1) | sQ8_eqProxy(X1,X0)) )),
% 2.09/0.64    inference(equality_proxy_axiom,[],[f58])).
% 2.09/0.64  fof(f130,plain,(
% 2.09/0.64    ~sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2))),
% 2.09/0.64    inference(subsumption_resolution,[],[f123,f19])).
% 2.09/0.64  fof(f19,plain,(
% 2.09/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.09/0.64    inference(cnf_transformation,[],[f13])).
% 2.09/0.64  fof(f123,plain,(
% 2.09/0.64    ~sQ8_eqProxy(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.09/0.64    inference(resolution,[],[f82,f61])).
% 2.09/0.64  fof(f61,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ8_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1))) )),
% 2.09/0.64    inference(equality_proxy_replacement,[],[f30,f58])).
% 2.09/0.64  fof(f30,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f15])).
% 2.09/0.64  fof(f15,plain,(
% 2.09/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f8])).
% 2.09/0.64  fof(f8,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.09/0.64  fof(f82,plain,(
% 2.09/0.64    ( ! [X0] : (~sQ8_eqProxy(X0,k3_subset_1(sK0,sK2)) | ~sQ8_eqProxy(sK1,X0)) )),
% 2.09/0.64    inference(resolution,[],[f60,f72])).
% 2.09/0.64  fof(f72,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~sQ8_eqProxy(X0,X1) | ~sQ8_eqProxy(X1,X2) | sQ8_eqProxy(X0,X2)) )),
% 2.09/0.64    inference(equality_proxy_axiom,[],[f58])).
% 2.09/0.64  fof(f60,plain,(
% 2.09/0.64    ~sQ8_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 2.09/0.64    inference(equality_proxy_replacement,[],[f20,f58])).
% 2.09/0.64  fof(f20,plain,(
% 2.09/0.64    sK1 != k3_subset_1(sK0,sK2)),
% 2.09/0.64    inference(cnf_transformation,[],[f13])).
% 2.09/0.64  fof(f1386,plain,(
% 2.09/0.64    r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1385,f253])).
% 2.09/0.64  fof(f253,plain,(
% 2.09/0.64    ~r2_hidden(sK7(sK0,sK2,sK1),sK2)),
% 2.09/0.64    inference(subsumption_resolution,[],[f247,f251])).
% 2.09/0.64  fof(f247,plain,(
% 2.09/0.64    ~r2_hidden(sK7(sK0,sK2,sK1),sK2) | r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(resolution,[],[f207,f67])).
% 2.09/0.64  fof(f67,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | sQ8_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 2.09/0.64    inference(equality_proxy_replacement,[],[f46,f58])).
% 2.09/0.64  fof(f46,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.64    inference(cnf_transformation,[],[f4])).
% 2.09/0.64  fof(f1385,plain,(
% 2.09/0.64    r2_hidden(sK7(sK0,sK2,sK1),sK2) | r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f1377])).
% 2.09/0.64  fof(f1377,plain,(
% 2.09/0.64    r2_hidden(sK7(sK0,sK2,sK1),sK2) | r2_hidden(sK7(sK0,sK2,sK1),sK1) | r2_hidden(sK7(sK0,sK2,sK1),sK1)),
% 2.09/0.64    inference(resolution,[],[f180,f207])).
% 2.09/0.64  fof(f180,plain,(
% 2.09/0.64    ( ! [X26,X25] : (sQ8_eqProxy(k4_xboole_0(sK0,X25),X26) | r2_hidden(sK7(sK0,X25,X26),sK2) | r2_hidden(sK7(sK0,X25,X26),X26) | r2_hidden(sK7(sK0,X25,X26),sK1)) )),
% 2.09/0.64    inference(resolution,[],[f88,f68])).
% 2.09/0.64  fof(f68,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | sQ8_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 2.09/0.64    inference(equality_proxy_replacement,[],[f45,f58])).
% 2.09/0.64  fof(f45,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.64    inference(cnf_transformation,[],[f4])).
% 2.09/0.64  fof(f88,plain,(
% 2.09/0.64    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 2.09/0.64    inference(subsumption_resolution,[],[f87,f24])).
% 2.09/0.64  fof(f87,plain,(
% 2.09/0.64    ( ! [X1] : (r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 2.09/0.64    inference(resolution,[],[f18,f28])).
% 2.09/0.64  fof(f18,plain,(
% 2.09/0.64    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f13])).
% 2.09/0.64  % SZS output end Proof for theBenchmark
% 2.09/0.64  % (10422)------------------------------
% 2.09/0.64  % (10422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (10422)Termination reason: Refutation
% 2.09/0.64  
% 2.09/0.64  % (10422)Memory used [KB]: 7036
% 2.09/0.64  % (10422)Time elapsed: 0.211 s
% 2.09/0.64  % (10422)------------------------------
% 2.09/0.64  % (10422)------------------------------
% 2.09/0.64  % (10408)Success in time 0.273 s
%------------------------------------------------------------------------------
