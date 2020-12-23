%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   76 (1414 expanded)
%              Number of leaves         :   11 ( 274 expanded)
%              Depth                    :   22
%              Number of atoms          :  222 (7305 expanded)
%              Number of equality atoms :   56 (1580 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(global_subsumption,[],[f197,f202,f203])).

fof(f203,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f139,f200])).

fof(f200,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f199,f187])).

fof(f187,plain,(
    k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f34,f159])).

% (5235)Termination reason: Refutation not found, incomplete strategy

% (5235)Memory used [KB]: 1663
% (5235)Time elapsed: 0.048 s
% (5235)------------------------------
% (5235)------------------------------
% (5239)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (5241)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f159,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f73,f144,f158])).

fof(f158,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f139,f92])).

fof(f92,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f78,f76])).

fof(f76,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f144,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f137,f92])).

fof(f137,plain,(
    v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f136,f79])).

fof(f79,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f133,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f121,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f119,f79])).

fof(f119,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f114,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f91,f38])).

fof(f38,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | v5_relat_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f89,f79])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(sK1,X0)
      | v5_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f83,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f83,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f37,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f73,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f33,f35])).

fof(f33,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f199,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f198,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f190,f50])).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f190,plain,
    ( ~ r1_tarski(k6_relat_1(k1_xboole_0),sK3)
    | sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f85,f187])).

fof(f85,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),sK3)
    | sK0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f80,f78])).

fof(f80,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),sK3)
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | k1_relset_1(X1,X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

fof(f139,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(subsumption_resolution,[],[f138,f79])).

fof(f138,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(subsumption_resolution,[],[f134,f35])).

fof(f134,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f202,plain,(
    v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f137,f200])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f188,f187])).

fof(f188,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f73,f187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (5232)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (5235)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (5233)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (5235)Refutation not found, incomplete strategy% (5235)------------------------------
% 0.20/0.54  % (5235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5240)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (5233)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(global_subsumption,[],[f197,f202,f203])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 0.20/0.54    inference(backward_demodulation,[],[f139,f200])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.54    inference(forward_demodulation,[],[f199,f187])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    k1_xboole_0 = sK0),
% 0.20/0.54    inference(global_subsumption,[],[f34,f159])).
% 0.20/0.54  % (5235)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5235)Memory used [KB]: 1663
% 0.20/0.54  % (5235)Time elapsed: 0.048 s
% 0.20/0.54  % (5235)------------------------------
% 0.20/0.54  % (5235)------------------------------
% 1.38/0.55  % (5239)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.38/0.55  % (5241)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.38/0.56  fof(f159,plain,(
% 1.38/0.56    k1_xboole_0 = sK1),
% 1.38/0.56    inference(global_subsumption,[],[f73,f144,f158])).
% 1.38/0.56  fof(f158,plain,(
% 1.38/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK1),
% 1.38/0.56    inference(superposition,[],[f139,f92])).
% 1.38/0.56  fof(f92,plain,(
% 1.38/0.56    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.38/0.56    inference(superposition,[],[f78,f76])).
% 1.38/0.56  fof(f76,plain,(
% 1.38/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.38/0.56    inference(subsumption_resolution,[],[f75,f37])).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,plain,(
% 1.38/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.38/0.56    inference(flattening,[],[f16])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.38/0.56    inference(ennf_transformation,[],[f15])).
% 1.38/0.56  fof(f15,negated_conjecture,(
% 1.38/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.38/0.56    inference(negated_conjecture,[],[f14])).
% 1.38/0.56  fof(f14,conjecture,(
% 1.38/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.38/0.56  fof(f75,plain,(
% 1.38/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.56    inference(resolution,[],[f36,f44])).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f19])).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(flattening,[],[f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f78,plain,(
% 1.38/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.38/0.56    inference(resolution,[],[f37,f45])).
% 1.38/0.56  fof(f45,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f20])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f9])).
% 1.38/0.56  fof(f9,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.56  fof(f144,plain,(
% 1.38/0.56    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK1),
% 1.38/0.56    inference(superposition,[],[f137,f92])).
% 1.38/0.56  fof(f137,plain,(
% 1.38/0.56    v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.38/0.56    inference(subsumption_resolution,[],[f136,f79])).
% 1.38/0.56  fof(f79,plain,(
% 1.38/0.56    v1_relat_1(sK3)),
% 1.38/0.56    inference(resolution,[],[f37,f52])).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.56  fof(f136,plain,(
% 1.38/0.56    ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.38/0.56    inference(subsumption_resolution,[],[f133,f35])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    v1_funct_1(sK3)),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f133,plain,(
% 1.38/0.56    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.38/0.56    inference(resolution,[],[f121,f53])).
% 1.38/0.56  fof(f53,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f25])).
% 1.38/0.56  fof(f25,plain,(
% 1.38/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(flattening,[],[f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.38/0.56    inference(ennf_transformation,[],[f13])).
% 1.38/0.56  fof(f13,axiom,(
% 1.38/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.38/0.56  fof(f121,plain,(
% 1.38/0.56    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.38/0.56    inference(subsumption_resolution,[],[f119,f79])).
% 1.38/0.56  fof(f119,plain,(
% 1.38/0.56    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 1.38/0.56    inference(resolution,[],[f114,f61])).
% 1.38/0.56  fof(f61,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f31])).
% 1.38/0.56  fof(f31,plain,(
% 1.38/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.38/0.56  fof(f114,plain,(
% 1.38/0.56    v5_relat_1(sK3,sK2)),
% 1.38/0.56    inference(resolution,[],[f91,f38])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    r1_tarski(sK1,sK2)),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f91,plain,(
% 1.38/0.56    ( ! [X0] : (~r1_tarski(sK1,X0) | v5_relat_1(sK3,X0)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f89,f79])).
% 1.38/0.56  fof(f89,plain,(
% 1.38/0.56    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(sK1,X0) | v5_relat_1(sK3,X0)) )),
% 1.38/0.56    inference(resolution,[],[f83,f59])).
% 1.38/0.56  fof(f59,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | v5_relat_1(X2,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f30])).
% 1.38/0.56  fof(f30,plain,(
% 1.38/0.56    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 1.38/0.56    inference(flattening,[],[f29])).
% 1.38/0.56  fof(f29,plain,(
% 1.38/0.56    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 1.38/0.56  fof(f83,plain,(
% 1.38/0.56    v5_relat_1(sK3,sK1)),
% 1.38/0.56    inference(resolution,[],[f37,f63])).
% 1.38/0.56  fof(f63,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f32])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.38/0.56  fof(f73,plain,(
% 1.38/0.56    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.38/0.56    inference(subsumption_resolution,[],[f33,f35])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f199,plain,(
% 1.38/0.56    sK0 = k1_relat_1(sK3)),
% 1.38/0.56    inference(subsumption_resolution,[],[f198,f49])).
% 1.38/0.56  fof(f49,plain,(
% 1.38/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.56  fof(f198,plain,(
% 1.38/0.56    ~r1_tarski(k1_xboole_0,sK3) | sK0 = k1_relat_1(sK3)),
% 1.38/0.56    inference(forward_demodulation,[],[f190,f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.38/0.56    inference(cnf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.38/0.56  fof(f190,plain,(
% 1.38/0.56    ~r1_tarski(k6_relat_1(k1_xboole_0),sK3) | sK0 = k1_relat_1(sK3)),
% 1.38/0.56    inference(backward_demodulation,[],[f85,f187])).
% 1.38/0.56  fof(f85,plain,(
% 1.38/0.56    ~r1_tarski(k6_relat_1(sK0),sK3) | sK0 = k1_relat_1(sK3)),
% 1.38/0.56    inference(forward_demodulation,[],[f80,f78])).
% 1.38/0.56  fof(f80,plain,(
% 1.38/0.56    ~r1_tarski(k6_relat_1(sK0),sK3) | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.38/0.56    inference(resolution,[],[f37,f57])).
% 1.38/0.56  fof(f57,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k6_relat_1(X1),X2) | k1_relset_1(X1,X0,X2) = X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f28])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.38/0.56    inference(flattening,[],[f27])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.38/0.56    inference(ennf_transformation,[],[f11])).
% 1.38/0.56  fof(f11,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).
% 1.38/0.56  fof(f139,plain,(
% 1.38/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.38/0.56    inference(subsumption_resolution,[],[f138,f79])).
% 1.38/0.56  fof(f138,plain,(
% 1.38/0.56    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.38/0.56    inference(subsumption_resolution,[],[f134,f35])).
% 1.38/0.56  fof(f134,plain,(
% 1.38/0.56    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.38/0.56    inference(resolution,[],[f121,f54])).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f25])).
% 1.38/0.56  fof(f202,plain,(
% 1.38/0.56    v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.38/0.56    inference(backward_demodulation,[],[f137,f200])).
% 1.38/0.56  fof(f197,plain,(
% 1.38/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.38/0.56    inference(forward_demodulation,[],[f188,f187])).
% 1.38/0.56  fof(f188,plain,(
% 1.38/0.56    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.38/0.56    inference(backward_demodulation,[],[f73,f187])).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (5233)------------------------------
% 1.38/0.56  % (5233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (5233)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (5233)Memory used [KB]: 6268
% 1.38/0.56  % (5233)Time elapsed: 0.114 s
% 1.38/0.56  % (5233)------------------------------
% 1.38/0.56  % (5233)------------------------------
% 1.38/0.56  % (5227)Success in time 0.197 s
%------------------------------------------------------------------------------
