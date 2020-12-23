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
% DateTime   : Thu Dec  3 13:06:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   75 (1501 expanded)
%              Number of leaves         :   11 ( 317 expanded)
%              Depth                    :   19
%              Number of atoms          :  204 (5806 expanded)
%              Number of equality atoms :   47 (1378 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13318)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (13335)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f374,f363])).

fof(f363,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f252,f359])).

fof(f359,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f355,f252])).

fof(f355,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f253,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f53,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f71,f27])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f67,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f62,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f52])).

% (13321)Refutation not found, incomplete strategy% (13321)------------------------------
% (13321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13321)Termination reason: Refutation not found, incomplete strategy

% (13321)Memory used [KB]: 6268
% (13321)Time elapsed: 0.142 s
% (13321)------------------------------
% (13321)------------------------------
fof(f52,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f253,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f243,f246])).

fof(f246,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f221,f27])).

fof(f221,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f72,f215])).

fof(f215,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f214,f55])).

fof(f55,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f54,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f54,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f23,f24])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f214,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f212,f26])).

fof(f26,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f212,plain,
    ( k1_xboole_0 = sK1
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f44,f25])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f57,f32])).

fof(f57,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

% (13317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f243,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f216,f73])).

fof(f216,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f25,f215])).

fof(f252,plain,(
    ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f218,f246])).

fof(f218,plain,(
    ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f215])).

fof(f374,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f373,f253])).

fof(f373,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f369,f73])).

fof(f369,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f368,f359])).

fof(f368,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(forward_demodulation,[],[f367,f359])).

fof(f367,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,sK0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f364,f27])).

fof(f364,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,sK0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(backward_demodulation,[],[f257,f359])).

fof(f257,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,sK0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_xboole_0(sK0) ) ),
    inference(forward_demodulation,[],[f250,f246])).

fof(f250,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_xboole_0(sK0)
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(backward_demodulation,[],[f159,f246])).

fof(f159,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | v1_funct_2(sK2,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f158,f98])).

fof(f98,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f46,f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (13346)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (13323)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13327)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (13322)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13319)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13319)Refutation not found, incomplete strategy% (13319)------------------------------
% 0.22/0.53  % (13319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13319)Memory used [KB]: 10746
% 0.22/0.53  % (13319)Time elapsed: 0.120 s
% 0.22/0.53  % (13319)------------------------------
% 0.22/0.53  % (13319)------------------------------
% 0.22/0.53  % (13323)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (13343)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (13344)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (13327)Refutation not found, incomplete strategy% (13327)------------------------------
% 0.22/0.54  % (13327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13327)Memory used [KB]: 10746
% 0.22/0.54  % (13327)Time elapsed: 0.126 s
% 0.22/0.54  % (13327)------------------------------
% 0.22/0.54  % (13327)------------------------------
% 0.22/0.54  % (13320)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (13342)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (13345)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (13325)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (13330)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (13325)Refutation not found, incomplete strategy% (13325)------------------------------
% 0.22/0.55  % (13325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13325)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13325)Memory used [KB]: 10746
% 0.22/0.55  % (13325)Time elapsed: 0.131 s
% 0.22/0.55  % (13325)------------------------------
% 0.22/0.55  % (13325)------------------------------
% 0.22/0.55  % (13331)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (13336)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (13337)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (13343)Refutation not found, incomplete strategy% (13343)------------------------------
% 0.22/0.55  % (13343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13321)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  % (13318)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.56  % (13335)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.56  fof(f375,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(subsumption_resolution,[],[f374,f363])).
% 1.46/0.56  fof(f363,plain,(
% 1.46/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.46/0.56    inference(backward_demodulation,[],[f252,f359])).
% 1.46/0.56  fof(f359,plain,(
% 1.46/0.56    k1_xboole_0 = sK0),
% 1.46/0.56    inference(resolution,[],[f355,f252])).
% 1.46/0.56  fof(f355,plain,(
% 1.46/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(resolution,[],[f253,f76])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.46/0.56    inference(backward_demodulation,[],[f53,f73])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.46/0.56    inference(resolution,[],[f71,f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    inference(cnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.46/0.56    inference(resolution,[],[f67,f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,plain,(
% 1.46/0.56    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.46/0.56  fof(f67,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(resolution,[],[f62,f59])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.46/0.56    inference(resolution,[],[f38,f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,plain,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(resolution,[],[f36,f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.46/0.56    inference(equality_resolution,[],[f52])).
% 1.46/0.56  % (13321)Refutation not found, incomplete strategy% (13321)------------------------------
% 1.46/0.56  % (13321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (13321)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (13321)Memory used [KB]: 6268
% 1.46/0.56  % (13321)Time elapsed: 0.142 s
% 1.46/0.56  % (13321)------------------------------
% 1.46/0.56  % (13321)------------------------------
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.46/0.56    inference(equality_resolution,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.46/0.56  fof(f253,plain,(
% 1.46/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.56    inference(backward_demodulation,[],[f243,f246])).
% 1.46/0.56  fof(f246,plain,(
% 1.46/0.56    k1_xboole_0 = sK2),
% 1.46/0.56    inference(subsumption_resolution,[],[f221,f27])).
% 1.46/0.56  fof(f221,plain,(
% 1.46/0.56    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2),
% 1.46/0.56    inference(backward_demodulation,[],[f72,f215])).
% 1.46/0.56  fof(f215,plain,(
% 1.46/0.56    k1_xboole_0 = sK1),
% 1.46/0.56    inference(subsumption_resolution,[],[f214,f55])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,sK0,sK1)),
% 1.46/0.56    inference(subsumption_resolution,[],[f54,f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    inference(cnf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,plain,(
% 1.46/0.56    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f13])).
% 1.46/0.56  fof(f13,plain,(
% 1.46/0.56    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,negated_conjecture,(
% 1.46/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.46/0.56    inference(negated_conjecture,[],[f11])).
% 1.46/0.56  fof(f11,conjecture,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    inference(subsumption_resolution,[],[f23,f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    v1_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f14])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    inference(cnf_transformation,[],[f14])).
% 1.46/0.56  fof(f214,plain,(
% 1.46/0.56    k1_xboole_0 = sK1 | v1_funct_2(sK2,sK0,sK1)),
% 1.46/0.56    inference(subsumption_resolution,[],[f212,f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f14])).
% 1.46/0.56  fof(f212,plain,(
% 1.46/0.56    k1_xboole_0 = sK1 | sK0 != k1_relset_1(sK0,sK1,sK2) | v1_funct_2(sK2,sK0,sK1)),
% 1.46/0.56    inference(resolution,[],[f44,f25])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f72,plain,(
% 1.46/0.56    ~v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 1.46/0.56    inference(resolution,[],[f67,f58])).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 1.46/0.56    inference(resolution,[],[f57,f32])).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 1.46/0.56    inference(resolution,[],[f29,f25])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f15])).
% 1.46/0.56  % (13317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.56  fof(f15,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.46/0.56  fof(f243,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.56    inference(forward_demodulation,[],[f216,f73])).
% 1.46/0.56  fof(f216,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.46/0.56    inference(backward_demodulation,[],[f25,f215])).
% 1.46/0.56  fof(f252,plain,(
% 1.46/0.56    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 1.46/0.56    inference(backward_demodulation,[],[f218,f246])).
% 1.46/0.56  fof(f218,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,sK0,k1_xboole_0)),
% 1.46/0.56    inference(backward_demodulation,[],[f55,f215])).
% 1.46/0.56  fof(f374,plain,(
% 1.46/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.46/0.56    inference(subsumption_resolution,[],[f373,f253])).
% 1.46/0.56  fof(f373,plain,(
% 1.46/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.46/0.56    inference(superposition,[],[f369,f73])).
% 1.46/0.56  fof(f369,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.46/0.56    inference(forward_demodulation,[],[f368,f359])).
% 1.46/0.56  fof(f368,plain,(
% 1.46/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.46/0.56    inference(forward_demodulation,[],[f367,f359])).
% 1.46/0.56  fof(f367,plain,(
% 1.46/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,sK0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f364,f27])).
% 1.46/0.56  fof(f364,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v1_funct_2(k1_xboole_0,sK0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.46/0.56    inference(backward_demodulation,[],[f257,f359])).
% 1.46/0.56  fof(f257,plain,(
% 1.46/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,sK0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_xboole_0(sK0)) )),
% 1.46/0.56    inference(forward_demodulation,[],[f250,f246])).
% 1.46/0.56  fof(f250,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_xboole_0(sK0) | v1_funct_2(sK2,sK0,X0)) )),
% 1.46/0.56    inference(backward_demodulation,[],[f159,f246])).
% 1.46/0.56  fof(f159,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_xboole_0(sK0) | v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.46/0.56    inference(resolution,[],[f158,f98])).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    v1_partfun1(sK2,sK0) | ~v1_xboole_0(sK0)),
% 1.46/0.56    inference(resolution,[],[f33,f25])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f17])).
% 1.46/0.56  fof(f17,plain,(
% 1.46/0.56    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 1.46/0.56  fof(f158,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK2,X0,X1)) )),
% 1.46/0.56    inference(resolution,[],[f46,f24])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (13323)------------------------------
% 1.46/0.56  % (13323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (13323)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (13328)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.56  % (13323)Memory used [KB]: 6396
% 1.46/0.56  % (13323)Time elapsed: 0.117 s
% 1.46/0.56  % (13323)------------------------------
% 1.46/0.56  % (13323)------------------------------
% 1.46/0.56  % (13316)Success in time 0.19 s
%------------------------------------------------------------------------------
