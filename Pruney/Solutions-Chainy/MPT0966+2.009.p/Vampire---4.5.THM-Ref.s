%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:38 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   77 (5229 expanded)
%              Number of leaves         :    6 ( 964 expanded)
%              Depth                    :   27
%              Number of atoms          :  210 (29229 expanded)
%              Number of equality atoms :   75 (7558 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f94])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f86,f90])).

fof(f90,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f18,f84])).

fof(f84,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f83,f72])).

fof(f72,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f17,f19])).

fof(f19,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

% (29462)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (29459)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

% (29477)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f17,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f68,f58])).

fof(f58,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f43,f46])).

fof(f46,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f20,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f20,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f57,f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ) ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f52,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f50,f19])).

fof(f50,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f49,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f49,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f22,f47])).

fof(f47,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f22,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f74,f58])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f67,f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ) ),
    inference(resolution,[],[f53,f25])).

fof(f53,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(subsumption_resolution,[],[f51,f19])).

fof(f51,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f21,f84])).

fof(f130,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f129,f119])).

fof(f119,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f118,f114])).

fof(f114,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f74,f108])).

fof(f108,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f95,f107])).

fof(f107,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f99,f94])).

fof(f99,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(resolution,[],[f93,f34])).

fof(f34,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f85,f90])).

fof(f85,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f84])).

fof(f95,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f87,f90])).

fof(f87,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f46,f84])).

fof(f118,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f98,f115])).

fof(f115,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f80,f108])).

fof(f80,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),sK2,sK3) ),
    inference(resolution,[],[f74,f27])).

fof(f98,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f92,f90])).

fof(f92,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f64,f90])).

fof(f64,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f129,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(subsumption_resolution,[],[f121,f93])).

fof(f121,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f97,f119])).

fof(f97,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f91,f90])).

fof(f91,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f39,f90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:45:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (29466)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (29464)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (29463)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (29473)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (29467)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (29478)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (29465)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.41/0.54  % (29479)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.41/0.54  % (29479)Refutation not found, incomplete strategy% (29479)------------------------------
% 1.41/0.54  % (29479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (29479)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (29479)Memory used [KB]: 10618
% 1.41/0.54  % (29479)Time elapsed: 0.121 s
% 1.41/0.54  % (29479)------------------------------
% 1.41/0.54  % (29479)------------------------------
% 1.41/0.54  % (29472)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.41/0.54  % (29472)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f131,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(subsumption_resolution,[],[f130,f94])).
% 1.41/0.54  fof(f94,plain,(
% 1.41/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.54    inference(backward_demodulation,[],[f86,f90])).
% 1.41/0.54  fof(f90,plain,(
% 1.41/0.54    k1_xboole_0 = sK0),
% 1.41/0.54    inference(trivial_inequality_removal,[],[f89])).
% 1.41/0.54  fof(f89,plain,(
% 1.41/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.41/0.54    inference(superposition,[],[f18,f84])).
% 1.41/0.54  fof(f84,plain,(
% 1.41/0.54    k1_xboole_0 = sK1),
% 1.41/0.54    inference(subsumption_resolution,[],[f83,f72])).
% 1.41/0.54  fof(f72,plain,(
% 1.41/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK1),
% 1.41/0.54    inference(resolution,[],[f71,f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.54    inference(subsumption_resolution,[],[f17,f19])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    v1_funct_1(sK3)),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.41/0.54    inference(flattening,[],[f8])).
% 1.41/0.55  % (29462)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.55  % (29459)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.41/0.55  fof(f8,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.41/0.55    inference(negated_conjecture,[],[f6])).
% 1.41/0.55  % (29477)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.41/0.55  fof(f6,conjecture,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK1),
% 1.41/0.55    inference(superposition,[],[f68,f58])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.41/0.55    inference(superposition,[],[f43,f46])).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.41/0.55    inference(resolution,[],[f21,f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f43,plain,(
% 1.41/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.41/0.55    inference(subsumption_resolution,[],[f42,f21])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.41/0.55    inference(resolution,[],[f20,f33])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f16])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(flattening,[],[f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f68,plain,(
% 1.41/0.55    v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.41/0.55    inference(resolution,[],[f57,f21])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK3,k1_relat_1(sK3),sK2)) )),
% 1.41/0.55    inference(resolution,[],[f52,f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f50,f19])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),sK2)),
% 1.41/0.55    inference(resolution,[],[f49,f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(flattening,[],[f10])).
% 1.41/0.55  fof(f10,plain,(
% 1.41/0.55    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.41/0.55    inference(backward_demodulation,[],[f22,f47])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.41/0.55    inference(resolution,[],[f21,f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f83,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK1),
% 1.41/0.55    inference(superposition,[],[f74,f58])).
% 1.41/0.55  fof(f74,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.41/0.55    inference(resolution,[],[f67,f21])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))) )),
% 1.41/0.55    inference(resolution,[],[f53,f25])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.41/0.55    inference(subsumption_resolution,[],[f51,f19])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.41/0.55    inference(resolution,[],[f49,f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f11])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f86,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.41/0.55    inference(backward_demodulation,[],[f21,f84])).
% 1.41/0.55  fof(f130,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.55    inference(forward_demodulation,[],[f129,f119])).
% 1.41/0.55  fof(f119,plain,(
% 1.41/0.55    k1_xboole_0 = sK2),
% 1.41/0.55    inference(subsumption_resolution,[],[f118,f114])).
% 1.41/0.55  fof(f114,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 1.41/0.55    inference(backward_demodulation,[],[f74,f108])).
% 1.41/0.55  fof(f108,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(sK3)),
% 1.41/0.55    inference(backward_demodulation,[],[f95,f107])).
% 1.41/0.55  fof(f107,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.41/0.55    inference(subsumption_resolution,[],[f99,f94])).
% 1.41/0.55  fof(f99,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.41/0.55    inference(resolution,[],[f93,f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.41/0.55    inference(equality_resolution,[],[f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f16])).
% 1.41/0.55  fof(f93,plain,(
% 1.41/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.41/0.55    inference(backward_demodulation,[],[f85,f90])).
% 1.41/0.55  fof(f85,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.41/0.55    inference(backward_demodulation,[],[f20,f84])).
% 1.41/0.55  fof(f95,plain,(
% 1.41/0.55    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.41/0.55    inference(backward_demodulation,[],[f87,f90])).
% 1.41/0.55  fof(f87,plain,(
% 1.41/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 1.41/0.55    inference(backward_demodulation,[],[f46,f84])).
% 1.41/0.55  fof(f118,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | k1_xboole_0 = sK2),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f117])).
% 1.41/0.55  fof(f117,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | k1_xboole_0 = sK2),
% 1.41/0.55    inference(backward_demodulation,[],[f98,f115])).
% 1.41/0.55  fof(f115,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)),
% 1.41/0.55    inference(backward_demodulation,[],[f80,f108])).
% 1.41/0.55  fof(f80,plain,(
% 1.41/0.55    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),sK2,sK3)),
% 1.41/0.55    inference(resolution,[],[f74,f27])).
% 1.41/0.55  fof(f98,plain,(
% 1.41/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | k1_xboole_0 = sK2),
% 1.41/0.55    inference(forward_demodulation,[],[f92,f90])).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3)),
% 1.41/0.55    inference(backward_demodulation,[],[f64,f90])).
% 1.41/0.55  fof(f64,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3)),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f63])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3)),
% 1.41/0.55    inference(resolution,[],[f39,f32])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f16])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 1.41/0.55    inference(subsumption_resolution,[],[f121,f93])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 1.41/0.55    inference(backward_demodulation,[],[f97,f119])).
% 1.41/0.55  fof(f97,plain,(
% 1.41/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.41/0.55    inference(forward_demodulation,[],[f91,f90])).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.55    inference(backward_demodulation,[],[f39,f90])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (29472)------------------------------
% 1.41/0.55  % (29472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (29472)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (29472)Memory used [KB]: 1663
% 1.41/0.55  % (29472)Time elapsed: 0.095 s
% 1.41/0.55  % (29472)------------------------------
% 1.41/0.55  % (29472)------------------------------
% 1.41/0.55  % (29458)Success in time 0.19 s
%------------------------------------------------------------------------------
