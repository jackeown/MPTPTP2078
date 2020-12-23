%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:44 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  101 (3468 expanded)
%              Number of leaves         :   12 ( 697 expanded)
%              Depth                    :   27
%              Number of atoms          :  302 (16283 expanded)
%              Number of equality atoms :   81 (3934 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(subsumption_resolution,[],[f350,f370])).

fof(f370,plain,(
    ! [X2] : v1_funct_2(sK3,k1_xboole_0,X2) ),
    inference(subsumption_resolution,[],[f369,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f369,plain,(
    ! [X2] :
      ( v1_funct_2(sK3,k1_xboole_0,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f368,f70])).

fof(f70,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f368,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK3)
      | v1_funct_2(sK3,k1_xboole_0,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f366,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f366,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,sK4(k1_xboole_0,X2,sK3))
      | ~ v1_relat_1(sK3)
      | v1_funct_2(sK3,k1_xboole_0,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f145,f330])).

fof(f330,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f314,f329])).

fof(f329,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f321,f274])).

fof(f274,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f255,f254])).

fof(f254,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f30,f253])).

fof(f253,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f236,f76])).

fof(f76,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f40,f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f236,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f34,f235])).

fof(f235,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f234,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f232,f153])).

fof(f153,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f152,f116])).

fof(f116,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f152,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f150,f32])).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f52,f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f232,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f231,f100])).

fof(f100,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(resolution,[],[f99,f58])).

fof(f99,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK3))
      | r1_tarski(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f98,f83])).

fof(f83,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f98,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK3))
      | r1_tarski(X2,sK2)
      | ~ v5_relat_1(sK3,sK1) ) ),
    inference(resolution,[],[f89,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK3),X0)
      | ~ v5_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f37,f70])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

% (6331)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f87,plain,(
    ! [X6] :
      ( r1_tarski(X6,sK2)
      | ~ r1_tarski(X6,sK1) ) ),
    inference(resolution,[],[f57,f34])).

fof(f231,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(resolution,[],[f230,f123])).

fof(f123,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f118,f100])).

fof(f118,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f117,f69])).

fof(f69,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f29,f31])).

fof(f29,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(sK3),X1)
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f42,f70])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f230,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,sK0,X0)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f229,f153])).

fof(f229,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f226,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X0,sK3) ) ),
    inference(resolution,[],[f119,f58])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X1)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | k1_relat_1(sK3) = k1_relset_1(X1,X0,sK3) ) ),
    inference(resolution,[],[f117,f44])).

fof(f226,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),X0,sK3)
      | v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f149,f58])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X1)
      | k1_relset_1(X1,X0,sK3) != X1
      | v1_funct_2(sK3,X1,X0)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f117])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f255,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f253])).

fof(f321,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f275,f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f275,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f256,f254])).

fof(f256,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f33,f253])).

fof(f314,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f264,f254])).

fof(f264,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f116,f253])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK4(k1_relat_1(X0),X1,X0))
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),X1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f66,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | v1_funct_2(X2,k1_relat_1(X2),X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK4(X0,X1,X2),X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f350,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f335,f35])).

fof(f335,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f273,f330])).

fof(f273,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f271,f254])).

fof(f271,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f123,f254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n015.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 12:46:53 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.17/0.43  % (6330)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.17/0.43  % (6339)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.17/0.44  % (6340)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.17/0.45  % (6340)Refutation found. Thanks to Tanya!
% 0.17/0.45  % SZS status Theorem for theBenchmark
% 0.17/0.45  % (6325)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.17/0.45  % (6332)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.17/0.45  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f371,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(subsumption_resolution,[],[f350,f370])).
% 0.17/0.45  fof(f370,plain,(
% 0.17/0.45    ( ! [X2] : (v1_funct_2(sK3,k1_xboole_0,X2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f369,f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    v1_funct_1(sK3)),
% 0.17/0.45    inference(cnf_transformation,[],[f15])).
% 0.17/0.45  fof(f15,plain,(
% 0.17/0.45    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.17/0.45    inference(flattening,[],[f14])).
% 0.17/0.45  fof(f14,plain,(
% 0.17/0.45    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.17/0.45    inference(ennf_transformation,[],[f13])).
% 0.17/0.45  fof(f13,negated_conjecture,(
% 0.17/0.45    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.17/0.45    inference(negated_conjecture,[],[f12])).
% 0.17/0.45  fof(f12,conjecture,(
% 0.17/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.17/0.45  fof(f369,plain,(
% 0.17/0.45    ( ! [X2] : (v1_funct_2(sK3,k1_xboole_0,X2) | ~v1_funct_1(sK3)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f368,f70])).
% 0.17/0.45  fof(f70,plain,(
% 0.17/0.45    v1_relat_1(sK3)),
% 0.17/0.45    inference(resolution,[],[f43,f33])).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.17/0.45    inference(cnf_transformation,[],[f15])).
% 0.17/0.45  fof(f43,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f20])).
% 0.17/0.45  fof(f20,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f6])).
% 0.17/0.45  fof(f6,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.17/0.45  fof(f368,plain,(
% 0.17/0.45    ( ! [X2] : (~v1_relat_1(sK3) | v1_funct_2(sK3,k1_xboole_0,X2) | ~v1_funct_1(sK3)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f366,f35])).
% 0.17/0.45  fof(f35,plain,(
% 0.17/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f3])).
% 0.17/0.45  fof(f3,axiom,(
% 0.17/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.17/0.45  fof(f366,plain,(
% 0.17/0.45    ( ! [X2] : (~r1_tarski(k1_xboole_0,sK4(k1_xboole_0,X2,sK3)) | ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_xboole_0,X2) | ~v1_funct_1(sK3)) )),
% 0.17/0.45    inference(superposition,[],[f145,f330])).
% 0.17/0.45  fof(f330,plain,(
% 0.17/0.45    k1_xboole_0 = k1_relat_1(sK3)),
% 0.17/0.45    inference(backward_demodulation,[],[f314,f329])).
% 0.17/0.45  fof(f329,plain,(
% 0.17/0.45    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.17/0.45    inference(subsumption_resolution,[],[f321,f274])).
% 0.17/0.45  fof(f274,plain,(
% 0.17/0.45    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.17/0.45    inference(forward_demodulation,[],[f255,f254])).
% 0.17/0.45  fof(f254,plain,(
% 0.17/0.45    k1_xboole_0 = sK0),
% 0.17/0.45    inference(subsumption_resolution,[],[f30,f253])).
% 0.17/0.45  fof(f253,plain,(
% 0.17/0.45    k1_xboole_0 = sK1),
% 0.17/0.45    inference(subsumption_resolution,[],[f236,f76])).
% 0.17/0.45  fof(f76,plain,(
% 0.17/0.45    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.17/0.45    inference(resolution,[],[f40,f35])).
% 0.17/0.45  fof(f40,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.17/0.45    inference(cnf_transformation,[],[f1])).
% 0.17/0.45  fof(f1,axiom,(
% 0.17/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.45  fof(f236,plain,(
% 0.17/0.45    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.17/0.45    inference(superposition,[],[f34,f235])).
% 0.17/0.45  fof(f235,plain,(
% 0.17/0.45    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.17/0.45    inference(subsumption_resolution,[],[f234,f58])).
% 0.17/0.45  fof(f58,plain,(
% 0.17/0.45    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.45    inference(equality_resolution,[],[f39])).
% 0.17/0.45  fof(f39,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.45    inference(cnf_transformation,[],[f1])).
% 0.17/0.45  fof(f234,plain,(
% 0.17/0.45    ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.17/0.45    inference(duplicate_literal_removal,[],[f233])).
% 0.17/0.45  fof(f233,plain,(
% 0.17/0.45    ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.17/0.45    inference(superposition,[],[f232,f153])).
% 0.17/0.45  fof(f153,plain,(
% 0.17/0.45    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.17/0.45    inference(superposition,[],[f152,f116])).
% 0.17/0.45  fof(f116,plain,(
% 0.17/0.45    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.17/0.45    inference(resolution,[],[f44,f33])).
% 0.17/0.45  fof(f44,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f21])).
% 0.17/0.45  fof(f21,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f8])).
% 0.17/0.45  fof(f8,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.17/0.45  fof(f152,plain,(
% 0.17/0.45    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.17/0.45    inference(subsumption_resolution,[],[f150,f32])).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    v1_funct_2(sK3,sK0,sK1)),
% 0.17/0.45    inference(cnf_transformation,[],[f15])).
% 0.17/0.45  fof(f150,plain,(
% 0.17/0.45    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.17/0.45    inference(resolution,[],[f52,f33])).
% 0.17/0.45  fof(f52,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f24])).
% 0.17/0.45  fof(f24,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(flattening,[],[f23])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f10])).
% 0.17/0.45  fof(f10,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.17/0.45  fof(f232,plain,(
% 0.17/0.45    ~r1_tarski(k1_relat_1(sK3),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.17/0.45    inference(subsumption_resolution,[],[f231,f100])).
% 0.17/0.45  fof(f100,plain,(
% 0.17/0.45    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.17/0.45    inference(resolution,[],[f99,f58])).
% 0.17/0.45  fof(f99,plain,(
% 0.17/0.45    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK3)) | r1_tarski(X2,sK2)) )),
% 0.17/0.45    inference(subsumption_resolution,[],[f98,f83])).
% 0.17/0.45  fof(f83,plain,(
% 0.17/0.45    v5_relat_1(sK3,sK1)),
% 0.17/0.45    inference(resolution,[],[f46,f33])).
% 0.17/0.45  fof(f46,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f22])).
% 0.17/0.45  fof(f22,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.45    inference(ennf_transformation,[],[f7])).
% 0.17/0.45  fof(f7,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.17/0.45  fof(f98,plain,(
% 0.17/0.45    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK3)) | r1_tarski(X2,sK2) | ~v5_relat_1(sK3,sK1)) )),
% 0.17/0.45    inference(resolution,[],[f89,f73])).
% 0.17/0.45  fof(f73,plain,(
% 0.17/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(sK3),X0) | ~v5_relat_1(sK3,X0)) )),
% 0.17/0.45    inference(resolution,[],[f37,f70])).
% 0.17/0.45  fof(f37,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f16])).
% 0.17/0.45  fof(f16,plain,(
% 0.17/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f4])).
% 0.17/0.45  fof(f4,axiom,(
% 0.17/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.17/0.46  % (6331)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.17/0.47  fof(f89,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0) | r1_tarski(X1,sK2)) )),
% 0.17/0.47    inference(resolution,[],[f87,f57])).
% 0.17/0.47  fof(f57,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f28])).
% 0.17/0.47  fof(f28,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.17/0.47    inference(flattening,[],[f27])).
% 0.17/0.47  fof(f27,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.17/0.47    inference(ennf_transformation,[],[f2])).
% 0.17/0.47  fof(f2,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.17/0.47  fof(f87,plain,(
% 0.17/0.47    ( ! [X6] : (r1_tarski(X6,sK2) | ~r1_tarski(X6,sK1)) )),
% 0.17/0.47    inference(resolution,[],[f57,f34])).
% 0.17/0.47  fof(f231,plain,(
% 0.17/0.47    ~r1_tarski(k2_relat_1(sK3),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(k1_relat_1(sK3),sK0)),
% 0.17/0.47    inference(resolution,[],[f230,f123])).
% 0.17/0.47  fof(f123,plain,(
% 0.17/0.47    ~v1_funct_2(sK3,sK0,sK2) | ~r1_tarski(k1_relat_1(sK3),sK0)),
% 0.17/0.47    inference(subsumption_resolution,[],[f118,f100])).
% 0.17/0.47  fof(f118,plain,(
% 0.17/0.47    ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),sK0) | ~v1_funct_2(sK3,sK0,sK2)),
% 0.17/0.47    inference(resolution,[],[f117,f69])).
% 0.17/0.47  fof(f69,plain,(
% 0.17/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2)),
% 0.17/0.47    inference(subsumption_resolution,[],[f29,f31])).
% 0.17/0.47  fof(f29,plain,(
% 0.17/0.47    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.17/0.47    inference(cnf_transformation,[],[f15])).
% 0.17/0.47  fof(f117,plain,(
% 0.17/0.47    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(sK3),X1) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 0.17/0.47    inference(resolution,[],[f42,f70])).
% 0.17/0.47  fof(f42,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.47    inference(cnf_transformation,[],[f19])).
% 0.17/0.47  fof(f19,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.17/0.47    inference(flattening,[],[f18])).
% 0.17/0.47  fof(f18,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.17/0.47    inference(ennf_transformation,[],[f9])).
% 0.17/0.47  fof(f9,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.17/0.47  fof(f230,plain,(
% 0.17/0.47    ( ! [X0] : (v1_funct_2(sK3,sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK1) )),
% 0.17/0.47    inference(superposition,[],[f229,f153])).
% 0.17/0.47  fof(f229,plain,(
% 0.17/0.47    ( ! [X0] : (v1_funct_2(sK3,k1_relat_1(sK3),X0) | ~r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = X0) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f226,f133])).
% 0.17/0.47  fof(f133,plain,(
% 0.17/0.47    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X0,sK3)) )),
% 0.17/0.47    inference(resolution,[],[f119,f58])).
% 0.17/0.47  fof(f119,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X1) | ~r1_tarski(k2_relat_1(sK3),X0) | k1_relat_1(sK3) = k1_relset_1(X1,X0,sK3)) )),
% 0.17/0.47    inference(resolution,[],[f117,f44])).
% 0.17/0.47  fof(f226,plain,(
% 0.17/0.47    ( ! [X0] : (k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),X0,sK3) | v1_funct_2(sK3,k1_relat_1(sK3),X0) | ~r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = X0) )),
% 0.17/0.47    inference(resolution,[],[f149,f58])).
% 0.17/0.47  fof(f149,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X1) | k1_relset_1(X1,X0,sK3) != X1 | v1_funct_2(sK3,X1,X0) | ~r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = X0) )),
% 0.17/0.47    inference(resolution,[],[f51,f117])).
% 0.17/0.47  fof(f51,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f34,plain,(
% 0.17/0.47    r1_tarski(sK1,sK2)),
% 0.17/0.47    inference(cnf_transformation,[],[f15])).
% 0.17/0.47  fof(f30,plain,(
% 0.17/0.47    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.17/0.47    inference(cnf_transformation,[],[f15])).
% 0.17/0.47  fof(f255,plain,(
% 0.17/0.47    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.17/0.47    inference(backward_demodulation,[],[f32,f253])).
% 0.17/0.47  fof(f321,plain,(
% 0.17/0.47    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.17/0.47    inference(resolution,[],[f275,f60])).
% 0.17/0.47  fof(f60,plain,(
% 0.17/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.17/0.47    inference(equality_resolution,[],[f50])).
% 0.17/0.47  fof(f50,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f275,plain,(
% 0.17/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.17/0.47    inference(forward_demodulation,[],[f256,f254])).
% 0.17/0.47  fof(f256,plain,(
% 0.17/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.17/0.47    inference(backward_demodulation,[],[f33,f253])).
% 0.17/0.47  fof(f314,plain,(
% 0.17/0.47    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.17/0.47    inference(forward_demodulation,[],[f264,f254])).
% 0.17/0.47  fof(f264,plain,(
% 0.17/0.47    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.17/0.47    inference(backward_demodulation,[],[f116,f253])).
% 0.17/0.47  fof(f145,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK4(k1_relat_1(X0),X1,X0)) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),X1) | ~v1_funct_1(X0)) )),
% 0.17/0.47    inference(resolution,[],[f66,f41])).
% 0.17/0.47  fof(f41,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f17])).
% 0.17/0.47  fof(f17,plain,(
% 0.17/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.17/0.47    inference(ennf_transformation,[],[f5])).
% 0.17/0.47  fof(f5,axiom,(
% 0.17/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.17/0.47  fof(f66,plain,(
% 0.17/0.47    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | v1_funct_2(X2,k1_relat_1(X2),X1)) )),
% 0.17/0.47    inference(equality_resolution,[],[f55])).
% 0.17/0.47  fof(f55,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK4(X0,X1,X2),X0) | v1_funct_2(X2,X0,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f26])).
% 0.17/0.47  fof(f26,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.17/0.47    inference(flattening,[],[f25])).
% 0.17/0.47  fof(f25,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.17/0.47    inference(ennf_transformation,[],[f11])).
% 0.17/0.47  fof(f11,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.17/0.47  fof(f350,plain,(
% 0.17/0.47    ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.17/0.47    inference(subsumption_resolution,[],[f335,f35])).
% 0.17/0.47  fof(f335,plain,(
% 0.17/0.47    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.17/0.47    inference(backward_demodulation,[],[f273,f330])).
% 0.17/0.47  fof(f273,plain,(
% 0.17/0.47    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.17/0.47    inference(forward_demodulation,[],[f271,f254])).
% 0.17/0.47  fof(f271,plain,(
% 0.17/0.47    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~r1_tarski(k1_relat_1(sK3),sK0)),
% 0.17/0.47    inference(backward_demodulation,[],[f123,f254])).
% 0.17/0.47  % SZS output end Proof for theBenchmark
% 0.17/0.47  % (6340)------------------------------
% 0.17/0.47  % (6340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.47  % (6340)Termination reason: Refutation
% 0.17/0.47  
% 0.17/0.47  % (6340)Memory used [KB]: 1791
% 0.17/0.47  % (6340)Time elapsed: 0.073 s
% 0.17/0.47  % (6340)------------------------------
% 0.17/0.47  % (6340)------------------------------
% 0.17/0.47  % (6323)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.17/0.47  % (6324)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.17/0.47  % (6320)Success in time 0.155 s
%------------------------------------------------------------------------------
