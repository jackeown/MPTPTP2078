%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 224 expanded)
%              Number of leaves         :    7 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 749 expanded)
%              Number of equality atoms :   13 ( 119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1150,f407])).

fof(f407,plain,(
    ~ r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f406,f404])).

fof(f404,plain,(
    ~ r2_hidden(sK4(sK0,sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f325,f63])).

fof(f63,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f62,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
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
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).

fof(f62,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f61,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f61,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f15,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
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

fof(f15,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f325,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f158,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f158,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f148,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f148,plain,(
    ~ sQ5_eqProxy(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f143,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f143,plain,
    ( ~ sQ5_eqProxy(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ5_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f26,f37])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ sQ5_eqProxy(X0,k3_subset_1(sK0,sK2))
      | ~ sQ5_eqProxy(sK1,X0) ) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | ~ sQ5_eqProxy(X1,X2)
      | sQ5_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f39,plain,(
    ~ sQ5_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f17,f37])).

fof(f17,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f406,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f323,f405])).

fof(f405,plain,(
    r2_hidden(sK4(sK0,sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f324,f51])).

fof(f324,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK0)
    | r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f158,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f323,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),sK0)
    | r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f158,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1150,plain,(
    r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1149,f404])).

fof(f1149,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f1141])).

fof(f1141,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | r2_hidden(sK4(sK0,sK2,sK1),sK1)
    | r2_hidden(sK4(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f156,f158])).

fof(f156,plain,(
    ! [X12,X11] :
      ( sQ5_eqProxy(k4_xboole_0(sK0,X11),X12)
      | r2_hidden(sK4(sK0,X11,X12),sK2)
      | r2_hidden(sK4(sK0,X11,X12),X12)
      | r2_hidden(sK4(sK0,X11,X12),sK1) ) ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f58,f20])).

fof(f58,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f14,f24])).

fof(f14,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (32692)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (32676)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (32671)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (32679)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (32699)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (32695)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (32675)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (32700)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (32673)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32687)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (32674)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32672)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (32683)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32678)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (32698)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32680)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (32691)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (32684)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (32693)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (32694)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (32677)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (32681)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32690)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (32682)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32688)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (32697)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (32681)Refutation not found, incomplete strategy% (32681)------------------------------
% 0.21/0.55  % (32681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32686)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (32689)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (32682)Refutation not found, incomplete strategy% (32682)------------------------------
% 0.21/0.56  % (32682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32685)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (32681)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32681)Memory used [KB]: 10618
% 0.21/0.56  % (32681)Time elapsed: 0.120 s
% 0.21/0.56  % (32681)------------------------------
% 0.21/0.56  % (32681)------------------------------
% 0.21/0.56  % (32693)Refutation not found, incomplete strategy% (32693)------------------------------
% 0.21/0.56  % (32693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32696)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (32693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32693)Memory used [KB]: 10746
% 0.21/0.56  % (32693)Time elapsed: 0.141 s
% 0.21/0.56  % (32693)------------------------------
% 0.21/0.56  % (32693)------------------------------
% 0.21/0.56  % (32682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32682)Memory used [KB]: 10618
% 0.21/0.56  % (32682)Time elapsed: 0.140 s
% 0.21/0.56  % (32682)------------------------------
% 0.21/0.56  % (32682)------------------------------
% 0.21/0.57  % (32688)Refutation not found, incomplete strategy% (32688)------------------------------
% 0.21/0.57  % (32688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32688)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32688)Memory used [KB]: 10618
% 0.21/0.57  % (32688)Time elapsed: 0.146 s
% 0.21/0.57  % (32688)------------------------------
% 0.21/0.57  % (32688)------------------------------
% 0.21/0.60  % (32684)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f1151,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(subsumption_resolution,[],[f1150,f407])).
% 0.21/0.60  fof(f407,plain,(
% 0.21/0.60    ~r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(subsumption_resolution,[],[f406,f404])).
% 0.21/0.60  fof(f404,plain,(
% 0.21/0.60    ~r2_hidden(sK4(sK0,sK2,sK1),sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f325,f63])).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f62,f51])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.21/0.60    inference(resolution,[],[f18,f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,plain,(
% 0.21/0.60    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(flattening,[],[f9])).
% 0.21/0.60  fof(f9,plain,(
% 0.21/0.60    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.60    inference(negated_conjecture,[],[f7])).
% 0.21/0.60  fof(f7,conjecture,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f61,f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.60    inference(resolution,[],[f15,f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f325,plain,(
% 0.21/0.60    ~r2_hidden(sK4(sK0,sK2,sK1),sK2) | r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(resolution,[],[f158,f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.60    inference(equality_proxy_replacement,[],[f30,f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.60    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.60  fof(f158,plain,(
% 0.21/0.60    ~sQ5_eqProxy(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.60    inference(resolution,[],[f148,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~sQ5_eqProxy(X0,X1) | sQ5_eqProxy(X1,X0)) )),
% 0.21/0.60    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.60  fof(f148,plain,(
% 0.21/0.60    ~sQ5_eqProxy(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.60    inference(subsumption_resolution,[],[f143,f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f143,plain,(
% 0.21/0.60    ~sQ5_eqProxy(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.60    inference(resolution,[],[f56,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ5_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1))) )),
% 0.21/0.60    inference(equality_proxy_replacement,[],[f26,f37])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X0] : (~sQ5_eqProxy(X0,k3_subset_1(sK0,sK2)) | ~sQ5_eqProxy(sK1,X0)) )),
% 0.21/0.60    inference(resolution,[],[f39,f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~sQ5_eqProxy(X0,X1) | ~sQ5_eqProxy(X1,X2) | sQ5_eqProxy(X0,X2)) )),
% 0.21/0.60    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ~sQ5_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.60    inference(equality_proxy_replacement,[],[f17,f37])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    sK1 != k3_subset_1(sK0,sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f406,plain,(
% 0.21/0.60    r2_hidden(sK4(sK0,sK2,sK1),sK2) | ~r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(subsumption_resolution,[],[f323,f405])).
% 0.21/0.60  fof(f405,plain,(
% 0.21/0.60    r2_hidden(sK4(sK0,sK2,sK1),sK0)),
% 0.21/0.60    inference(subsumption_resolution,[],[f324,f51])).
% 0.21/0.60  fof(f324,plain,(
% 0.21/0.60    r2_hidden(sK4(sK0,sK2,sK1),sK0) | r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(resolution,[],[f158,f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.60    inference(equality_proxy_replacement,[],[f29,f37])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f323,plain,(
% 0.21/0.60    ~r2_hidden(sK4(sK0,sK2,sK1),sK0) | r2_hidden(sK4(sK0,sK2,sK1),sK2) | ~r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(resolution,[],[f158,f43])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.60    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f1150,plain,(
% 0.21/0.60    r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(subsumption_resolution,[],[f1149,f404])).
% 0.21/0.60  fof(f1149,plain,(
% 0.21/0.60    r2_hidden(sK4(sK0,sK2,sK1),sK2) | r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f1141])).
% 0.21/0.60  fof(f1141,plain,(
% 0.21/0.60    r2_hidden(sK4(sK0,sK2,sK1),sK2) | r2_hidden(sK4(sK0,sK2,sK1),sK1) | r2_hidden(sK4(sK0,sK2,sK1),sK1)),
% 0.21/0.60    inference(resolution,[],[f156,f158])).
% 0.21/0.60  fof(f156,plain,(
% 0.21/0.60    ( ! [X12,X11] : (sQ5_eqProxy(k4_xboole_0(sK0,X11),X12) | r2_hidden(sK4(sK0,X11,X12),sK2) | r2_hidden(sK4(sK0,X11,X12),X12) | r2_hidden(sK4(sK0,X11,X12),sK1)) )),
% 0.21/0.60    inference(resolution,[],[f59,f42])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f58,f20])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ( ! [X1] : (r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.60    inference(resolution,[],[f14,f24])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (32684)------------------------------
% 0.21/0.60  % (32684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (32684)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (32684)Memory used [KB]: 6652
% 0.21/0.60  % (32684)Time elapsed: 0.180 s
% 0.21/0.60  % (32684)------------------------------
% 0.21/0.60  % (32684)------------------------------
% 0.21/0.60  % (32670)Success in time 0.234 s
%------------------------------------------------------------------------------
