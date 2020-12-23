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
% DateTime   : Thu Dec  3 13:00:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 267 expanded)
%              Number of leaves         :    7 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 (1075 expanded)
%              Number of equality atoms :   19 ( 248 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(global_subsumption,[],[f143,f150])).

fof(f150,plain,(
    ~ r2_hidden(sK4(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f92,f126])).

fof(f126,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f18,f72,f82,f71,f19,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(sK2,X1,X2)
      | r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X2
      | ~ r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f17,f75])).

% (17614)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X2
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f31,f16])).

fof(f16,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

% (17588)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ~ r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f68,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f68,plain,(
    ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f65,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f65,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f20,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    r2_hidden(sK3(sK4(sK1,k2_relset_1(sK0,sK1,sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f72,f15])).

fof(f15,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f68,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,(
    ~ r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f21,f71,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f143,plain,(
    r2_hidden(sK4(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f72,f126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.51  % (17593)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (17597)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (17601)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (17587)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (17595)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  % (17585)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (17613)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (17608)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (17609)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (17599)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (17590)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (17586)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (17589)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (17596)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (17591)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (17600)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (17611)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (17604)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (17602)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  % (17592)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (17607)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (17603)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (17609)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % (17605)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f161,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(global_subsumption,[],[f143,f150])).
% 0.19/0.53  fof(f150,plain,(
% 0.19/0.53    ~r2_hidden(sK4(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2)),k1_xboole_0)),
% 0.19/0.53    inference(backward_demodulation,[],[f92,f126])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    k1_xboole_0 = sK1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f18,f72,f82,f71,f19,f76])).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X2 | ~r2_hidden(X0,sK1)) )),
% 0.19/0.53    inference(global_subsumption,[],[f17,f75])).
% 0.19/0.53  % (17614)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  fof(f75,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X2 | ~v1_funct_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 0.19/0.53    inference(superposition,[],[f31,f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,plain,(
% 0.19/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.53    inference(flattening,[],[f9])).
% 0.19/0.53  fof(f9,plain,(
% 0.19/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.53    inference(ennf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.19/0.53    inference(negated_conjecture,[],[f7])).
% 0.19/0.53  fof(f7,conjecture,(
% 0.19/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.53    inference(flattening,[],[f13])).
% 0.19/0.53  fof(f13,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  % (17588)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    v1_funct_1(sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f71,plain,(
% 0.19/0.53    ~r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k2_relset_1(sK0,sK1,sK2))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f68,f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,plain,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.53  fof(f68,plain,(
% 0.19/0.53    ~r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f20,f65,f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.53  fof(f65,plain,(
% 0.19/0.53    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f61,f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f19,f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.53    inference(ennf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f82,plain,(
% 0.19/0.53    r2_hidden(sK3(sK4(sK1,k2_relset_1(sK0,sK1,sK2))),sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f72,f15])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f68,f26])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    ~r2_hidden(sK4(sK1,k2_relset_1(sK0,sK1,sK2)),k1_xboole_0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f21,f71,f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.53  fof(f143,plain,(
% 0.19/0.53    r2_hidden(sK4(k1_xboole_0,k2_relset_1(sK0,k1_xboole_0,sK2)),k1_xboole_0)),
% 0.19/0.53    inference(backward_demodulation,[],[f72,f126])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (17609)------------------------------
% 0.19/0.53  % (17609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (17609)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (17609)Memory used [KB]: 6268
% 0.19/0.53  % (17609)Time elapsed: 0.130 s
% 0.19/0.53  % (17609)------------------------------
% 0.19/0.53  % (17609)------------------------------
% 0.19/0.53  % (17594)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (17605)Refutation not found, incomplete strategy% (17605)------------------------------
% 0.19/0.53  % (17605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (17605)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (17605)Memory used [KB]: 10746
% 0.19/0.53  % (17605)Time elapsed: 0.138 s
% 0.19/0.53  % (17605)------------------------------
% 0.19/0.53  % (17605)------------------------------
% 0.19/0.54  % (17584)Success in time 0.177 s
%------------------------------------------------------------------------------
