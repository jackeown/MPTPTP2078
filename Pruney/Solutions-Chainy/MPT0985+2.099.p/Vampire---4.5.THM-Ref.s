%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:15 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  158 (12143 expanded)
%              Number of leaves         :   15 (2396 expanded)
%              Depth                    :   42
%              Number of atoms          :  394 (55642 expanded)
%              Number of equality atoms :  101 (8808 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f737,plain,(
    $false ),
    inference(subsumption_resolution,[],[f736,f138])).

fof(f138,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f99,f135])).

% (10661)Refutation not found, incomplete strategy% (10661)------------------------------
% (10661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10661)Termination reason: Refutation not found, incomplete strategy

% (10661)Memory used [KB]: 10618
% (10661)Time elapsed: 0.172 s
% (10661)------------------------------
% (10661)------------------------------
fof(f135,plain,(
    ! [X1] : k1_xboole_0 = sK5(X1,k1_xboole_0) ),
    inference(resolution,[],[f132,f101])).

fof(f101,plain,(
    ! [X0] : r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f99,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f118,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f118,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f56,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f99,plain,(
    ! [X0] : m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f65,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f736,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f735,f720])).

fof(f720,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f719,f80])).

fof(f719,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f718,f320])).

fof(f320,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f319,f313])).

fof(f313,plain,(
    ! [X2] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f312,f152])).

fof(f152,plain,(
    ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    inference(superposition,[],[f68,f136])).

fof(f136,plain,(
    ! [X2] : k1_xboole_0 = sK5(k1_xboole_0,X2) ),
    inference(resolution,[],[f132,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(sK5(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f100,f61])).

fof(f100,plain,(
    ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f65,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f312,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(resolution,[],[f87,f138])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

% (10663)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (10662)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f14,axiom,(
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

fof(f319,plain,(
    ! [X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X1,k1_xboole_0) ),
    inference(superposition,[],[f244,f136])).

fof(f244,plain,(
    ! [X4,X5] : k1_relset_1(X4,X5,sK5(X4,X5)) = k1_relat_1(sK5(X4,X5)) ),
    inference(resolution,[],[f70,f65])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f718,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f717,f655])).

fof(f655,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f654,f80])).

fof(f654,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f653,f592])).

fof(f592,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f591,f105])).

fof(f105,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f591,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f590,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f590,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f580,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f580,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f37,f551,f557])).

fof(f557,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f269,f548])).

fof(f548,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f546,f243])).

fof(f243,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f70,f40])).

fof(f546,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f541,f39])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f541,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f77,f40])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f269,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f259,f216])).

fof(f216,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f205,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f205,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f201,f204])).

fof(f204,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f203,f105])).

fof(f203,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f202,f38])).

fof(f202,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f201,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) ),
    inference(subsumption_resolution,[],[f200,f105])).

fof(f200,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f198,f38])).

fof(f198,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f197,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f197,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) ),
    inference(subsumption_resolution,[],[f196,f105])).

fof(f196,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f195,f38])).

fof(f195,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f192,f48])).

fof(f192,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) ),
    inference(superposition,[],[f186,f191])).

fof(f191,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f190,f105])).

fof(f190,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f189,f38])).

fof(f189,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f186,plain,(
    ! [X1] :
      ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f46,f61])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f259,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f207,f256])).

fof(f256,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f251,f42])).

fof(f42,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f251,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f71,f40])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

% (10672)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

% (10651)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f207,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f194,f204])).

fof(f194,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f45,f191])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f551,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f262,f548])).

fof(f262,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f221,f256])).

fof(f221,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f220,f105])).

fof(f220,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f219,f38])).

fof(f219,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f218,f216])).

fof(f218,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f208,f48])).

fof(f208,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f193,f204])).

fof(f193,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f46,f191])).

fof(f37,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f653,plain,(
    sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f652,f177])).

fof(f177,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f176,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f174,f43])).

fof(f174,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_xboole_0(X7)
      | r1_tarski(X6,X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f158,f52])).

fof(f158,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f57,f58])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f652,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f598,f80])).

fof(f598,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f119,f592])).

fof(f119,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f56,f93])).

fof(f93,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f61,f40])).

fof(f717,plain,(
    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f716,f177])).

fof(f716,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f715,f81])).

fof(f715,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f616,f655])).

fof(f616,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f271,f592])).

fof(f271,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f261,f256])).

fof(f261,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f217,f256])).

fof(f217,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f205,f56])).

fof(f735,plain,(
    ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f734,f152])).

fof(f734,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f733,f720])).

fof(f733,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f723,f146])).

fof(f146,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f67,f135])).

fof(f67,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f723,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f669,f720])).

% (10652)Refutation not found, incomplete strategy% (10652)------------------------------
% (10652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10652)Termination reason: Refutation not found, incomplete strategy

% (10652)Memory used [KB]: 10874
% (10652)Time elapsed: 0.181 s
% (10652)------------------------------
% (10652)------------------------------
fof(f669,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f668,f655])).

fof(f668,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f663,f655])).

fof(f663,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f649,f655])).

fof(f649,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f648,f81])).

fof(f648,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f593,f592])).

fof(f593,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f37,f592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n004.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 16:45:38 EST 2020
% 0.07/0.28  % CPUTime    : 
% 0.13/0.47  % (10674)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.13/0.47  % (10665)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.13/0.47  % (10673)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.13/0.48  % (10664)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.13/0.48  % (10656)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.13/0.48  % (10657)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.13/0.50  % (10658)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.13/0.51  % (10659)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.13/0.51  % (10652)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.13/0.51  % (10653)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.13/0.51  % (10650)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.13/0.52  % (10679)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.13/0.53  % (10654)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.13/0.53  % (10670)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.13/0.53  % (10658)Refutation not found, incomplete strategy% (10658)------------------------------
% 0.13/0.53  % (10658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.53  % (10658)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.53  
% 0.13/0.53  % (10658)Memory used [KB]: 10746
% 0.13/0.53  % (10658)Time elapsed: 0.165 s
% 0.13/0.53  % (10658)------------------------------
% 0.13/0.53  % (10658)------------------------------
% 0.13/0.53  % (10661)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.13/0.53  % (10655)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.13/0.53  % (10671)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.13/0.54  % (10656)Refutation found. Thanks to Tanya!
% 0.13/0.54  % SZS status Theorem for theBenchmark
% 0.13/0.54  % SZS output start Proof for theBenchmark
% 0.13/0.54  fof(f737,plain,(
% 0.13/0.54    $false),
% 0.13/0.54    inference(subsumption_resolution,[],[f736,f138])).
% 0.13/0.54  fof(f138,plain,(
% 0.13/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.54    inference(backward_demodulation,[],[f99,f135])).
% 0.13/0.54  % (10661)Refutation not found, incomplete strategy% (10661)------------------------------
% 0.13/0.54  % (10661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.54  % (10661)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.54  
% 0.13/0.54  % (10661)Memory used [KB]: 10618
% 0.13/0.54  % (10661)Time elapsed: 0.172 s
% 0.13/0.54  % (10661)------------------------------
% 0.13/0.54  % (10661)------------------------------
% 0.13/0.54  fof(f135,plain,(
% 0.13/0.54    ( ! [X1] : (k1_xboole_0 = sK5(X1,k1_xboole_0)) )),
% 0.13/0.54    inference(resolution,[],[f132,f101])).
% 0.13/0.54  fof(f101,plain,(
% 0.13/0.54    ( ! [X0] : (r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.13/0.54    inference(resolution,[],[f99,f61])).
% 0.13/0.54  fof(f61,plain,(
% 0.13/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f7])).
% 0.13/0.54  fof(f7,axiom,(
% 0.13/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.13/0.54  fof(f132,plain,(
% 0.13/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.13/0.54    inference(resolution,[],[f118,f43])).
% 0.13/0.54  fof(f43,plain,(
% 0.13/0.54    v1_xboole_0(k1_xboole_0)),
% 0.13/0.54    inference(cnf_transformation,[],[f3])).
% 0.13/0.54  fof(f3,axiom,(
% 0.13/0.54    v1_xboole_0(k1_xboole_0)),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.13/0.54  fof(f118,plain,(
% 0.13/0.54    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 0.13/0.54    inference(resolution,[],[f56,f95])).
% 0.13/0.54  fof(f95,plain,(
% 0.13/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.13/0.54    inference(resolution,[],[f58,f52])).
% 0.13/0.54  fof(f52,plain,(
% 0.13/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f1])).
% 0.13/0.54  fof(f1,axiom,(
% 0.13/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.13/0.54  fof(f58,plain,(
% 0.13/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f31])).
% 0.13/0.54  fof(f31,plain,(
% 0.13/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.13/0.54    inference(ennf_transformation,[],[f2])).
% 0.13/0.54  fof(f2,axiom,(
% 0.13/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.13/0.54  fof(f56,plain,(
% 0.13/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.13/0.54    inference(cnf_transformation,[],[f5])).
% 0.13/0.54  fof(f5,axiom,(
% 0.13/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.13/0.54  fof(f99,plain,(
% 0.13/0.54    ( ! [X0] : (m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.13/0.54    inference(superposition,[],[f65,f80])).
% 0.13/0.54  fof(f80,plain,(
% 0.13/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.13/0.54    inference(equality_resolution,[],[f64])).
% 0.13/0.54  fof(f64,plain,(
% 0.13/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f6])).
% 0.13/0.54  fof(f6,axiom,(
% 0.13/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.13/0.54  fof(f65,plain,(
% 0.13/0.54    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.13/0.54    inference(cnf_transformation,[],[f20])).
% 0.13/0.54  fof(f20,plain,(
% 0.13/0.54    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(pure_predicate_removal,[],[f19])).
% 0.13/0.54  fof(f19,plain,(
% 0.13/0.54    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.13/0.54  fof(f15,axiom,(
% 0.13/0.54    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.13/0.54  fof(f736,plain,(
% 0.13/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.54    inference(forward_demodulation,[],[f735,f720])).
% 0.13/0.54  fof(f720,plain,(
% 0.13/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.13/0.54    inference(forward_demodulation,[],[f719,f80])).
% 0.13/0.54  fof(f719,plain,(
% 0.13/0.54    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0)),
% 0.13/0.54    inference(forward_demodulation,[],[f718,f320])).
% 0.13/0.54  fof(f320,plain,(
% 0.13/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.13/0.54    inference(forward_demodulation,[],[f319,f313])).
% 0.13/0.54  fof(f313,plain,(
% 0.13/0.54    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)) )),
% 0.13/0.54    inference(subsumption_resolution,[],[f312,f152])).
% 0.13/0.54  fof(f152,plain,(
% 0.13/0.54    ( ! [X2] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.13/0.54    inference(superposition,[],[f68,f136])).
% 0.13/0.54  fof(f136,plain,(
% 0.13/0.54    ( ! [X2] : (k1_xboole_0 = sK5(k1_xboole_0,X2)) )),
% 0.13/0.54    inference(resolution,[],[f132,f102])).
% 0.13/0.54  fof(f102,plain,(
% 0.13/0.54    ( ! [X0] : (r1_tarski(sK5(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.13/0.54    inference(resolution,[],[f100,f61])).
% 0.13/0.54  fof(f100,plain,(
% 0.13/0.54    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.13/0.54    inference(superposition,[],[f65,f81])).
% 0.13/0.54  fof(f81,plain,(
% 0.13/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.13/0.54    inference(equality_resolution,[],[f63])).
% 0.13/0.54  fof(f63,plain,(
% 0.13/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f6])).
% 0.13/0.54  fof(f68,plain,(
% 0.13/0.54    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f20])).
% 0.13/0.54  fof(f312,plain,(
% 0.13/0.54    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.13/0.54    inference(resolution,[],[f87,f138])).
% 0.13/0.54  fof(f87,plain,(
% 0.13/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.13/0.54    inference(forward_demodulation,[],[f82,f81])).
% 0.13/0.54  fof(f82,plain,(
% 0.13/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.13/0.54    inference(equality_resolution,[],[f75])).
% 0.13/0.54  fof(f75,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f36])).
% 0.13/0.54  fof(f36,plain,(
% 0.13/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(flattening,[],[f35])).
% 0.13/0.54  fof(f35,plain,(
% 0.13/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(ennf_transformation,[],[f14])).
% 0.13/0.54  % (10663)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.13/0.54  % (10662)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.13/0.54  fof(f14,axiom,(
% 0.13/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.13/0.54  fof(f319,plain,(
% 0.13/0.54    ( ! [X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)) )),
% 0.13/0.54    inference(superposition,[],[f244,f136])).
% 0.13/0.54  fof(f244,plain,(
% 0.13/0.54    ( ! [X4,X5] : (k1_relset_1(X4,X5,sK5(X4,X5)) = k1_relat_1(sK5(X4,X5))) )),
% 0.13/0.54    inference(resolution,[],[f70,f65])).
% 0.13/0.54  fof(f70,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f33])).
% 0.13/0.54  fof(f33,plain,(
% 0.13/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(ennf_transformation,[],[f12])).
% 0.13/0.54  fof(f12,axiom,(
% 0.13/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.13/0.54  fof(f718,plain,(
% 0.13/0.54    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))),
% 0.13/0.54    inference(forward_demodulation,[],[f717,f655])).
% 0.13/0.54  fof(f655,plain,(
% 0.13/0.54    k1_xboole_0 = sK2),
% 0.13/0.54    inference(forward_demodulation,[],[f654,f80])).
% 0.13/0.54  fof(f654,plain,(
% 0.13/0.54    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.13/0.54    inference(forward_demodulation,[],[f653,f592])).
% 0.13/0.54  fof(f592,plain,(
% 0.13/0.54    k1_xboole_0 = sK1),
% 0.13/0.54    inference(subsumption_resolution,[],[f591,f105])).
% 0.13/0.54  fof(f105,plain,(
% 0.13/0.54    v1_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f69,f40])).
% 0.13/0.54  fof(f40,plain,(
% 0.13/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.13/0.54    inference(cnf_transformation,[],[f22])).
% 0.13/0.54  fof(f22,plain,(
% 0.13/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.13/0.54    inference(flattening,[],[f21])).
% 0.13/0.54  fof(f21,plain,(
% 0.13/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.13/0.54    inference(ennf_transformation,[],[f18])).
% 0.13/0.54  fof(f18,negated_conjecture,(
% 0.13/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.13/0.54    inference(negated_conjecture,[],[f17])).
% 0.13/0.54  fof(f17,conjecture,(
% 0.13/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.13/0.54  fof(f69,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f32])).
% 0.13/0.54  fof(f32,plain,(
% 0.13/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(ennf_transformation,[],[f10])).
% 0.13/0.54  fof(f10,axiom,(
% 0.13/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.13/0.54  fof(f591,plain,(
% 0.13/0.54    k1_xboole_0 = sK1 | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f590,f38])).
% 0.13/0.54  fof(f38,plain,(
% 0.13/0.54    v1_funct_1(sK2)),
% 0.13/0.54    inference(cnf_transformation,[],[f22])).
% 0.13/0.54  fof(f590,plain,(
% 0.13/0.54    k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f580,f48])).
% 0.13/0.54  fof(f48,plain,(
% 0.13/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f27])).
% 0.13/0.54  fof(f27,plain,(
% 0.13/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.54    inference(flattening,[],[f26])).
% 0.13/0.54  fof(f26,plain,(
% 0.13/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.54    inference(ennf_transformation,[],[f8])).
% 0.13/0.54  fof(f8,axiom,(
% 0.13/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.13/0.54  fof(f580,plain,(
% 0.13/0.54    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 0.13/0.54    inference(global_subsumption,[],[f37,f551,f557])).
% 0.13/0.54  fof(f557,plain,(
% 0.13/0.54    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 0.13/0.54    inference(superposition,[],[f269,f548])).
% 0.13/0.54  fof(f548,plain,(
% 0.13/0.54    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.13/0.54    inference(superposition,[],[f546,f243])).
% 0.13/0.54  fof(f243,plain,(
% 0.13/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.13/0.54    inference(resolution,[],[f70,f40])).
% 0.13/0.54  fof(f546,plain,(
% 0.13/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.13/0.54    inference(subsumption_resolution,[],[f541,f39])).
% 0.13/0.54  fof(f39,plain,(
% 0.13/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.13/0.54    inference(cnf_transformation,[],[f22])).
% 0.13/0.54  fof(f541,plain,(
% 0.13/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.13/0.54    inference(resolution,[],[f77,f40])).
% 0.13/0.54  fof(f77,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f36])).
% 0.13/0.54  fof(f269,plain,(
% 0.13/0.54    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(subsumption_resolution,[],[f259,f216])).
% 0.13/0.54  fof(f216,plain,(
% 0.13/0.54    v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(resolution,[],[f205,f106])).
% 0.13/0.54  fof(f106,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 0.13/0.54    inference(resolution,[],[f69,f60])).
% 0.13/0.54  fof(f60,plain,(
% 0.13/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f7])).
% 0.13/0.54  fof(f205,plain,(
% 0.13/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))),
% 0.13/0.54    inference(backward_demodulation,[],[f201,f204])).
% 0.13/0.54  fof(f204,plain,(
% 0.13/0.54    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f203,f105])).
% 0.13/0.54  fof(f203,plain,(
% 0.13/0.54    ~v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f202,f38])).
% 0.13/0.54  fof(f202,plain,(
% 0.13/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f50,f41])).
% 0.13/0.54  fof(f41,plain,(
% 0.13/0.54    v2_funct_1(sK2)),
% 0.13/0.54    inference(cnf_transformation,[],[f22])).
% 0.13/0.54  fof(f50,plain,(
% 0.13/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.13/0.54    inference(cnf_transformation,[],[f29])).
% 0.13/0.54  fof(f29,plain,(
% 0.13/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.54    inference(flattening,[],[f28])).
% 0.13/0.54  fof(f28,plain,(
% 0.13/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.54    inference(ennf_transformation,[],[f9])).
% 0.13/0.54  fof(f9,axiom,(
% 0.13/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.13/0.54  fof(f201,plain,(
% 0.13/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))),
% 0.13/0.54    inference(subsumption_resolution,[],[f200,f105])).
% 0.13/0.54  fof(f200,plain,(
% 0.13/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f198,f38])).
% 0.13/0.54  fof(f198,plain,(
% 0.13/0.54    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f197,f47])).
% 0.13/0.54  fof(f47,plain,(
% 0.13/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f27])).
% 0.13/0.54  fof(f197,plain,(
% 0.13/0.54    ~v1_relat_1(k2_funct_1(sK2)) | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))),
% 0.13/0.54    inference(subsumption_resolution,[],[f196,f105])).
% 0.13/0.54  fof(f196,plain,(
% 0.13/0.54    ~v1_relat_1(k2_funct_1(sK2)) | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f195,f38])).
% 0.13/0.54  fof(f195,plain,(
% 0.13/0.54    ~v1_relat_1(k2_funct_1(sK2)) | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f192,f48])).
% 0.13/0.54  fof(f192,plain,(
% 0.13/0.54    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))),
% 0.13/0.54    inference(superposition,[],[f186,f191])).
% 0.13/0.54  fof(f191,plain,(
% 0.13/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(subsumption_resolution,[],[f190,f105])).
% 0.13/0.54  fof(f190,plain,(
% 0.13/0.54    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(subsumption_resolution,[],[f189,f38])).
% 0.13/0.54  fof(f189,plain,(
% 0.13/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(resolution,[],[f49,f41])).
% 0.13/0.54  fof(f49,plain,(
% 0.13/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.13/0.54    inference(cnf_transformation,[],[f29])).
% 0.13/0.54  fof(f186,plain,(
% 0.13/0.54    ( ! [X1] : (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_funct_1(X1)) )),
% 0.13/0.54    inference(resolution,[],[f46,f61])).
% 0.13/0.54  fof(f46,plain,(
% 0.13/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f25])).
% 0.13/0.54  fof(f25,plain,(
% 0.13/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.54    inference(flattening,[],[f24])).
% 0.13/0.54  fof(f24,plain,(
% 0.13/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.54    inference(ennf_transformation,[],[f16])).
% 0.13/0.54  fof(f16,axiom,(
% 0.13/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.13/0.54  fof(f259,plain,(
% 0.13/0.54    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(backward_demodulation,[],[f207,f256])).
% 0.13/0.54  fof(f256,plain,(
% 0.13/0.54    sK1 = k2_relat_1(sK2)),
% 0.13/0.54    inference(forward_demodulation,[],[f251,f42])).
% 0.13/0.54  fof(f42,plain,(
% 0.13/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.13/0.54    inference(cnf_transformation,[],[f22])).
% 0.13/0.54  fof(f251,plain,(
% 0.13/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f71,f40])).
% 0.13/0.54  fof(f71,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f34])).
% 0.13/0.54  % (10672)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.13/0.54  fof(f34,plain,(
% 0.13/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.54    inference(ennf_transformation,[],[f13])).
% 0.13/0.54  fof(f13,axiom,(
% 0.13/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.13/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.13/0.54  % (10651)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.13/0.54  fof(f207,plain,(
% 0.13/0.54    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(backward_demodulation,[],[f194,f204])).
% 0.13/0.54  fof(f194,plain,(
% 0.13/0.54    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(superposition,[],[f45,f191])).
% 0.13/0.54  fof(f45,plain,(
% 0.13/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f25])).
% 0.13/0.54  fof(f551,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.13/0.54    inference(superposition,[],[f262,f548])).
% 0.13/0.54  fof(f262,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.13/0.54    inference(backward_demodulation,[],[f221,f256])).
% 0.13/0.54  fof(f221,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.13/0.54    inference(subsumption_resolution,[],[f220,f105])).
% 0.13/0.54  fof(f220,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f219,f38])).
% 0.13/0.54  fof(f219,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(subsumption_resolution,[],[f218,f216])).
% 0.13/0.54  fof(f218,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.13/0.54    inference(resolution,[],[f208,f48])).
% 0.13/0.54  fof(f208,plain,(
% 0.13/0.54    ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(backward_demodulation,[],[f193,f204])).
% 0.13/0.54  fof(f193,plain,(
% 0.13/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(superposition,[],[f46,f191])).
% 0.13/0.54  fof(f37,plain,(
% 0.13/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.13/0.54    inference(cnf_transformation,[],[f22])).
% 0.13/0.54  fof(f653,plain,(
% 0.13/0.54    sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.13/0.54    inference(subsumption_resolution,[],[f652,f177])).
% 0.13/0.54  fof(f177,plain,(
% 0.13/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.13/0.54    inference(resolution,[],[f176,f78])).
% 0.13/0.54  fof(f78,plain,(
% 0.13/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.13/0.54    inference(equality_resolution,[],[f55])).
% 0.13/0.54  fof(f55,plain,(
% 0.13/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.13/0.54    inference(cnf_transformation,[],[f5])).
% 0.13/0.54  fof(f176,plain,(
% 0.13/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 0.13/0.54    inference(resolution,[],[f174,f43])).
% 0.13/0.54  fof(f174,plain,(
% 0.13/0.54    ( ! [X6,X8,X7] : (~v1_xboole_0(X7) | r1_tarski(X6,X8) | ~r1_tarski(X6,X7)) )),
% 0.13/0.54    inference(resolution,[],[f158,f52])).
% 0.13/0.54  fof(f158,plain,(
% 0.13/0.54    ( ! [X4,X2,X3] : (r2_hidden(sK4(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 0.13/0.54    inference(resolution,[],[f57,f58])).
% 0.13/0.54  fof(f57,plain,(
% 0.13/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.13/0.54    inference(cnf_transformation,[],[f31])).
% 0.13/0.54  fof(f652,plain,(
% 0.13/0.54    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.13/0.54    inference(forward_demodulation,[],[f598,f80])).
% 0.13/0.54  fof(f598,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.13/0.54    inference(backward_demodulation,[],[f119,f592])).
% 0.13/0.54  fof(f119,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.13/0.54    inference(resolution,[],[f56,f93])).
% 0.13/0.54  fof(f93,plain,(
% 0.13/0.54    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.13/0.54    inference(resolution,[],[f61,f40])).
% 0.13/0.54  fof(f717,plain,(
% 0.13/0.54    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.13/0.54    inference(subsumption_resolution,[],[f716,f177])).
% 0.13/0.54  fof(f716,plain,(
% 0.13/0.54    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.13/0.54    inference(forward_demodulation,[],[f715,f81])).
% 0.13/0.54  fof(f715,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.13/0.54    inference(forward_demodulation,[],[f616,f655])).
% 0.13/0.54  fof(f616,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.13/0.54    inference(backward_demodulation,[],[f271,f592])).
% 0.13/0.54  fof(f271,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.13/0.54    inference(forward_demodulation,[],[f261,f256])).
% 0.13/0.54  fof(f261,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.13/0.54    inference(backward_demodulation,[],[f217,f256])).
% 0.13/0.54  fof(f217,plain,(
% 0.13/0.54    ~r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.13/0.54    inference(resolution,[],[f205,f56])).
% 0.13/0.54  fof(f735,plain,(
% 0.13/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.54    inference(subsumption_resolution,[],[f734,f152])).
% 0.13/0.54  fof(f734,plain,(
% 0.13/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.54    inference(forward_demodulation,[],[f733,f720])).
% 0.13/0.54  fof(f733,plain,(
% 0.13/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.54    inference(subsumption_resolution,[],[f723,f146])).
% 0.13/0.54  fof(f146,plain,(
% 0.13/0.54    v1_funct_1(k1_xboole_0)),
% 0.13/0.54    inference(superposition,[],[f67,f135])).
% 0.13/0.54  fof(f67,plain,(
% 0.13/0.54    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 0.13/0.54    inference(cnf_transformation,[],[f20])).
% 0.13/0.54  fof(f723,plain,(
% 0.13/0.54    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.54    inference(backward_demodulation,[],[f669,f720])).
% 0.13/0.54  % (10652)Refutation not found, incomplete strategy% (10652)------------------------------
% 0.13/0.54  % (10652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.54  % (10652)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.54  
% 0.13/0.54  % (10652)Memory used [KB]: 10874
% 0.13/0.54  % (10652)Time elapsed: 0.181 s
% 0.13/0.54  % (10652)------------------------------
% 0.13/0.54  % (10652)------------------------------
% 0.13/0.54  fof(f669,plain,(
% 0.13/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.13/0.54    inference(forward_demodulation,[],[f668,f655])).
% 0.13/0.54  fof(f668,plain,(
% 0.13/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.13/0.54    inference(forward_demodulation,[],[f663,f655])).
% 0.13/0.54  fof(f663,plain,(
% 0.13/0.54    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.13/0.54    inference(backward_demodulation,[],[f649,f655])).
% 0.13/0.54  fof(f649,plain,(
% 0.13/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(forward_demodulation,[],[f648,f81])).
% 0.13/0.54  fof(f648,plain,(
% 0.13/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.13/0.54    inference(forward_demodulation,[],[f593,f592])).
% 0.13/0.54  fof(f593,plain,(
% 0.13/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.13/0.54    inference(backward_demodulation,[],[f37,f592])).
% 0.13/0.54  % SZS output end Proof for theBenchmark
% 0.13/0.54  % (10656)------------------------------
% 0.13/0.54  % (10656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.54  % (10656)Termination reason: Refutation
% 0.13/0.54  
% 0.13/0.54  % (10656)Memory used [KB]: 6652
% 0.13/0.54  % (10656)Time elapsed: 0.144 s
% 0.13/0.54  % (10656)------------------------------
% 0.13/0.54  % (10656)------------------------------
% 0.13/0.54  % (10649)Success in time 0.248 s
%------------------------------------------------------------------------------
