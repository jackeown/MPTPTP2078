%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
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
fof(f793,plain,(
    $false ),
    inference(subsumption_resolution,[],[f792,f205])).

fof(f205,plain,(
    ~ r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f204,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f84,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f67,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f21,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f66,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

% (18498)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(f204,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f199,f75])).

fof(f75,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f74,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f74,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f17,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

% (18502)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f17,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f199,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f167,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f37,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f167,plain,(
    ~ sQ7_eqProxy(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f110,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sQ7_eqProxy(X0,X1)
      | sQ7_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f48])).

fof(f110,plain,(
    ~ sQ7_eqProxy(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f103,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f103,plain,
    ( ~ sQ7_eqProxy(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ7_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f29,f48])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f69,plain,(
    ! [X0] :
      ( ~ sQ7_eqProxy(X0,k3_subset_1(sK0,sK2))
      | ~ sQ7_eqProxy(sK1,X0) ) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ7_eqProxy(X0,X1)
      | ~ sQ7_eqProxy(X1,X2)
      | sQ7_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f48])).

fof(f50,plain,(
    ~ sQ7_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f19,f48])).

fof(f19,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f792,plain,(
    r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f791,f207])).

fof(f207,plain,(
    ~ r2_hidden(sK6(sK0,sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f201,f205])).

fof(f201,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f167,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f39,f48])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f791,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f783])).

fof(f783,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),sK1)
    | r2_hidden(sK6(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f120,f167])).

fof(f120,plain,(
    ! [X14,X13] :
      ( sQ7_eqProxy(k4_xboole_0(sK0,X13),X14)
      | r2_hidden(sK6(sK0,X13,X14),sK2)
      | r2_hidden(sK6(sK0,X13,X14),X14)
      | r2_hidden(sK6(sK0,X13,X14),sK1) ) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f38,f48])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f71,f23])).

fof(f71,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f16,f27])).

fof(f16,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (18500)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.49  % (18496)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (18488)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (18491)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (18490)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (18492)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (18515)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.51  % (18508)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (18512)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.51  % (18504)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (18509)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (18501)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (18499)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (18510)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (18489)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (18487)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (18493)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (18511)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (18509)Refutation not found, incomplete strategy% (18509)------------------------------
% 0.19/0.52  % (18509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (18509)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (18509)Memory used [KB]: 10746
% 0.19/0.52  % (18509)Time elapsed: 0.086 s
% 0.19/0.52  % (18509)------------------------------
% 0.19/0.52  % (18509)------------------------------
% 0.19/0.52  % (18507)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (18514)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (18516)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (18513)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (18494)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (18495)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.53  % (18503)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (18497)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (18505)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.54  % (18506)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (18500)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f793,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(subsumption_resolution,[],[f792,f205])).
% 0.19/0.54  fof(f205,plain,(
% 0.19/0.54    ~r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(subsumption_resolution,[],[f204,f99])).
% 0.19/0.54  fof(f99,plain,(
% 0.19/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.19/0.54    inference(resolution,[],[f84,f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.54  fof(f84,plain,(
% 0.19/0.54    r1_tarski(sK1,sK0)),
% 0.19/0.54    inference(resolution,[],[f67,f43])).
% 0.19/0.54  fof(f43,plain,(
% 0.19/0.54    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.54    inference(equality_resolution,[],[f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.54  fof(f67,plain,(
% 0.19/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(subsumption_resolution,[],[f66,f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.54  fof(f66,plain,(
% 0.19/0.54    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(resolution,[],[f20,f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f13])).
% 0.19/0.54  fof(f13,plain,(
% 0.19/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.54  % (18498)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(cnf_transformation,[],[f12])).
% 0.19/0.54  fof(f12,plain,(
% 0.19/0.54    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.54    inference(flattening,[],[f11])).
% 0.19/0.54  fof(f11,plain,(
% 0.19/0.54    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f10])).
% 0.19/0.54  fof(f10,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.19/0.54    inference(negated_conjecture,[],[f9])).
% 0.19/0.54  fof(f9,conjecture,(
% 0.19/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).
% 0.19/0.54  fof(f204,plain,(
% 0.19/0.54    ~r2_hidden(sK6(sK0,sK2,sK1),sK0) | ~r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(subsumption_resolution,[],[f199,f75])).
% 0.19/0.54  fof(f75,plain,(
% 0.19/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f74,f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.54  fof(f74,plain,(
% 0.19/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.19/0.54    inference(resolution,[],[f17,f27])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f13])).
% 0.19/0.54  % (18502)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f12])).
% 0.19/0.54  fof(f199,plain,(
% 0.19/0.54    ~r2_hidden(sK6(sK0,sK2,sK1),sK0) | r2_hidden(sK6(sK0,sK2,sK1),sK2) | ~r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(resolution,[],[f167,f56])).
% 0.19/0.54  fof(f56,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | sQ7_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.54    inference(equality_proxy_replacement,[],[f37,f48])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.19/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.54  fof(f167,plain,(
% 0.19/0.54    ~sQ7_eqProxy(k4_xboole_0(sK0,sK2),sK1)),
% 0.19/0.54    inference(resolution,[],[f110,f58])).
% 0.19/0.54  fof(f58,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~sQ7_eqProxy(X0,X1) | sQ7_eqProxy(X1,X0)) )),
% 0.19/0.54    inference(equality_proxy_axiom,[],[f48])).
% 0.19/0.54  fof(f110,plain,(
% 0.19/0.54    ~sQ7_eqProxy(sK1,k4_xboole_0(sK0,sK2))),
% 0.19/0.54    inference(subsumption_resolution,[],[f103,f18])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(cnf_transformation,[],[f12])).
% 0.19/0.54  fof(f103,plain,(
% 0.19/0.54    ~sQ7_eqProxy(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(resolution,[],[f69,f51])).
% 0.19/0.54  fof(f51,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ7_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1))) )),
% 0.19/0.54    inference(equality_proxy_replacement,[],[f29,f48])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.54  fof(f69,plain,(
% 0.19/0.54    ( ! [X0] : (~sQ7_eqProxy(X0,k3_subset_1(sK0,sK2)) | ~sQ7_eqProxy(sK1,X0)) )),
% 0.19/0.54    inference(resolution,[],[f50,f59])).
% 0.19/0.54  fof(f59,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~sQ7_eqProxy(X0,X1) | ~sQ7_eqProxy(X1,X2) | sQ7_eqProxy(X0,X2)) )),
% 0.19/0.54    inference(equality_proxy_axiom,[],[f48])).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    ~sQ7_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 0.19/0.54    inference(equality_proxy_replacement,[],[f19,f48])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    sK1 != k3_subset_1(sK0,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f12])).
% 0.19/0.54  fof(f792,plain,(
% 0.19/0.54    r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(subsumption_resolution,[],[f791,f207])).
% 0.19/0.54  fof(f207,plain,(
% 0.19/0.54    ~r2_hidden(sK6(sK0,sK2,sK1),sK2)),
% 0.19/0.54    inference(subsumption_resolution,[],[f201,f205])).
% 0.19/0.54  fof(f201,plain,(
% 0.19/0.54    ~r2_hidden(sK6(sK0,sK2,sK1),sK2) | r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(resolution,[],[f167,f54])).
% 0.19/0.54  fof(f54,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | sQ7_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.54    inference(equality_proxy_replacement,[],[f39,f48])).
% 0.19/0.54  fof(f39,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f3])).
% 0.19/0.54  fof(f791,plain,(
% 0.19/0.54    r2_hidden(sK6(sK0,sK2,sK1),sK2) | r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f783])).
% 0.19/0.54  fof(f783,plain,(
% 0.19/0.54    r2_hidden(sK6(sK0,sK2,sK1),sK2) | r2_hidden(sK6(sK0,sK2,sK1),sK1) | r2_hidden(sK6(sK0,sK2,sK1),sK1)),
% 0.19/0.54    inference(resolution,[],[f120,f167])).
% 0.19/0.54  fof(f120,plain,(
% 0.19/0.54    ( ! [X14,X13] : (sQ7_eqProxy(k4_xboole_0(sK0,X13),X14) | r2_hidden(sK6(sK0,X13,X14),sK2) | r2_hidden(sK6(sK0,X13,X14),X14) | r2_hidden(sK6(sK0,X13,X14),sK1)) )),
% 0.19/0.54    inference(resolution,[],[f72,f55])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | sQ7_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.54    inference(equality_proxy_replacement,[],[f38,f48])).
% 0.19/0.54  fof(f38,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f3])).
% 0.19/0.54  fof(f72,plain,(
% 0.19/0.54    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f71,f23])).
% 0.19/0.54  fof(f71,plain,(
% 0.19/0.54    ( ! [X1] : (r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.19/0.54    inference(resolution,[],[f16,f27])).
% 0.19/0.54  fof(f16,plain,(
% 0.19/0.54    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f12])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (18500)------------------------------
% 0.19/0.54  % (18500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (18500)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (18500)Memory used [KB]: 6524
% 0.19/0.54  % (18500)Time elapsed: 0.139 s
% 0.19/0.54  % (18500)------------------------------
% 0.19/0.54  % (18500)------------------------------
% 0.19/0.54  % (18486)Success in time 0.186 s
%------------------------------------------------------------------------------
