%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  134 (75659 expanded)
%              Number of leaves         :   12 (15008 expanded)
%              Depth                    :   46
%              Number of atoms          :  344 (385597 expanded)
%              Number of equality atoms :  148 (114392 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(subsumption_resolution,[],[f552,f444])).

fof(f444,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f419,f424])).

fof(f424,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f423,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f423,plain,(
    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f422,f353])).

fof(f353,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f349,f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f349,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f348,f281])).

fof(f281,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f280,f252])).

fof(f252,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f149,f153])).

fof(f153,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f150,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f150,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f143,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f143,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f112,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f125,f107])).

fof(f107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f103,f88])).

fof(f88,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f43,f85])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f101,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f100,f89])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f86,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f52,f98])).

fof(f98,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f82,f83])).

fof(f83,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f42,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f124,f80])).

fof(f80,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f38,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f124,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f123,f98])).

fof(f123,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f109,f108])).

fof(f108,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f107,f68])).

fof(f109,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f107,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f107,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f146,f71])).

fof(f146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f107,f128])).

fof(f280,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f147,f153])).

fof(f147,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f132,f71])).

fof(f132,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f80,f128])).

fof(f348,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f341,f39])).

fof(f341,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(resolution,[],[f301,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f301,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f244,f153])).

fof(f244,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f241,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f103,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f93,f128])).

fof(f93,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f422,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f421,f51])).

fof(f421,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f361,f72])).

fof(f361,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f95,f353])).

fof(f95,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f87,f49])).

fof(f87,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f42,f54])).

fof(f419,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f418,f416])).

fof(f416,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f355,f72])).

fof(f355,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f42,f353])).

fof(f418,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f417,f72])).

fof(f417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f356,f353])).

fof(f356,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f80,f353])).

fof(f552,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f545,f550])).

fof(f550,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(X0,sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f542,f514])).

fof(f514,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f513,f443])).

fof(f443,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f416,f424])).

fof(f513,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f512,f72])).

fof(f512,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(forward_demodulation,[],[f510,f441])).

fof(f441,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f358,f424])).

fof(f358,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(backward_demodulation,[],[f83,f353])).

fof(f510,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(resolution,[],[f439,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f439,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f354,f424])).

fof(f354,plain,(
    v1_funct_2(sK3,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f41,f353])).

fof(f542,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,sK2,k1_xboole_0) ),
    inference(resolution,[],[f537,f68])).

fof(f537,plain,(
    ! [X3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) ),
    inference(resolution,[],[f525,f426])).

fof(f426,plain,(
    r1_tarski(k2_relat_1(k1_xboole_0),sK2) ),
    inference(backward_demodulation,[],[f88,f424])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f524,f427])).

fof(f427,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f89,f424])).

fof(f524,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f523,f51])).

fof(f523,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f52,f514])).

fof(f545,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(resolution,[],[f537,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.51  % (20284)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (20285)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.51  % (20305)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (20301)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.51  % (20297)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.51  % (20300)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.51  % (20291)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.52  % (20289)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.52  % (20299)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.52  % (20303)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (20283)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (20295)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (20307)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.53  % (20288)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (20283)Refutation not found, incomplete strategy% (20283)------------------------------
% 0.23/0.53  % (20283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (20283)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (20283)Memory used [KB]: 10618
% 0.23/0.53  % (20283)Time elapsed: 0.117 s
% 0.23/0.53  % (20283)------------------------------
% 0.23/0.53  % (20283)------------------------------
% 0.23/0.53  % (20293)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (20292)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.53  % (20287)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.53  % (20282)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  % (20288)Refutation not found, incomplete strategy% (20288)------------------------------
% 0.23/0.53  % (20288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (20288)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (20288)Memory used [KB]: 10618
% 0.23/0.53  % (20288)Time elapsed: 0.092 s
% 0.23/0.53  % (20288)------------------------------
% 0.23/0.53  % (20288)------------------------------
% 0.23/0.53  % (20286)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.54  % (20304)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.54  % (20290)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.54  % (20294)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.54  % (20296)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.55  % (20306)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.55  % (20302)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.55  % (20298)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.56  % (20287)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % SZS output start Proof for theBenchmark
% 0.23/0.56  fof(f553,plain,(
% 0.23/0.56    $false),
% 0.23/0.56    inference(subsumption_resolution,[],[f552,f444])).
% 0.23/0.56  fof(f444,plain,(
% 0.23/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 0.23/0.56    inference(backward_demodulation,[],[f419,f424])).
% 0.23/0.56  fof(f424,plain,(
% 0.23/0.56    k1_xboole_0 = sK3),
% 0.23/0.56    inference(forward_demodulation,[],[f423,f72])).
% 0.23/0.56  fof(f72,plain,(
% 0.23/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f45])).
% 0.23/0.56  fof(f45,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.56  fof(f423,plain,(
% 0.23/0.56    sK3 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.23/0.56    inference(forward_demodulation,[],[f422,f353])).
% 0.23/0.56  fof(f353,plain,(
% 0.23/0.56    k1_xboole_0 = sK0),
% 0.23/0.56    inference(subsumption_resolution,[],[f349,f39])).
% 0.23/0.56  fof(f39,plain,(
% 0.23/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.23/0.56    inference(cnf_transformation,[],[f25])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.23/0.56    inference(flattening,[],[f24])).
% 0.23/0.56  fof(f24,plain,(
% 0.23/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.23/0.56    inference(ennf_transformation,[],[f22])).
% 0.23/0.56  fof(f22,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.23/0.56    inference(negated_conjecture,[],[f21])).
% 0.23/0.56  fof(f21,conjecture,(
% 0.23/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.23/0.56  fof(f349,plain,(
% 0.23/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(resolution,[],[f348,f281])).
% 0.23/0.56  fof(f281,plain,(
% 0.23/0.56    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(subsumption_resolution,[],[f280,f252])).
% 0.23/0.56  fof(f252,plain,(
% 0.23/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f251])).
% 0.23/0.56  fof(f251,plain,(
% 0.23/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f149,f153])).
% 0.23/0.56  fof(f153,plain,(
% 0.23/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(resolution,[],[f150,f50])).
% 0.23/0.56  fof(f50,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.23/0.56    inference(ennf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.23/0.56  fof(f150,plain,(
% 0.23/0.56    r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f143,f71])).
% 0.23/0.56  fof(f71,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.56    inference(equality_resolution,[],[f46])).
% 0.23/0.56  fof(f46,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  fof(f143,plain,(
% 0.23/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f141])).
% 0.23/0.56  fof(f141,plain,(
% 0.23/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f112,f128])).
% 0.23/0.56  fof(f128,plain,(
% 0.23/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(subsumption_resolution,[],[f125,f107])).
% 0.23/0.56  fof(f107,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(resolution,[],[f103,f88])).
% 0.23/0.56  fof(f88,plain,(
% 0.23/0.56    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.23/0.56    inference(backward_demodulation,[],[f43,f85])).
% 0.23/0.56  fof(f85,plain,(
% 0.23/0.56    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.23/0.56    inference(resolution,[],[f42,f56])).
% 0.23/0.56  fof(f56,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f29])).
% 0.23/0.56  fof(f29,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f18])).
% 0.23/0.56  fof(f18,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.56    inference(cnf_transformation,[],[f25])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.23/0.56    inference(cnf_transformation,[],[f25])).
% 0.23/0.56  fof(f103,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(resolution,[],[f101,f74])).
% 0.23/0.56  fof(f74,plain,(
% 0.23/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f47])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.56  fof(f101,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f100,f89])).
% 0.23/0.56  fof(f89,plain,(
% 0.23/0.56    v1_relat_1(sK3)),
% 0.23/0.56    inference(subsumption_resolution,[],[f86,f58])).
% 0.23/0.56  fof(f58,plain,(
% 0.23/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f13,axiom,(
% 0.23/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.56  fof(f86,plain,(
% 0.23/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.23/0.56    inference(resolution,[],[f42,f57])).
% 0.23/0.56  fof(f57,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f30])).
% 0.23/0.56  fof(f30,plain,(
% 0.23/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(ennf_transformation,[],[f10])).
% 0.23/0.56  fof(f10,axiom,(
% 0.23/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.56  fof(f100,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(superposition,[],[f52,f98])).
% 0.23/0.56  fof(f98,plain,(
% 0.23/0.56    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f82,f83])).
% 0.23/0.56  fof(f83,plain,(
% 0.23/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.23/0.56    inference(resolution,[],[f42,f68])).
% 0.23/0.56  fof(f68,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f36])).
% 0.23/0.56  fof(f36,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f17])).
% 0.23/0.56  fof(f17,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.56  fof(f82,plain,(
% 0.23/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(subsumption_resolution,[],[f81,f42])).
% 0.23/0.56  fof(f81,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.56    inference(resolution,[],[f41,f64])).
% 0.23/0.56  fof(f64,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(flattening,[],[f31])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.56    inference(ennf_transformation,[],[f20])).
% 0.23/0.56  fof(f20,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.23/0.56    inference(cnf_transformation,[],[f25])).
% 0.23/0.56  fof(f52,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f28])).
% 0.23/0.56  fof(f28,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.23/0.56    inference(flattening,[],[f27])).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.23/0.56    inference(ennf_transformation,[],[f19])).
% 0.23/0.56  fof(f19,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.23/0.56  fof(f125,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.56    inference(resolution,[],[f124,f80])).
% 0.23/0.56  fof(f80,plain,(
% 0.23/0.56    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.56    inference(subsumption_resolution,[],[f38,f40])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    v1_funct_1(sK3)),
% 0.23/0.56    inference(cnf_transformation,[],[f25])).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.56    inference(cnf_transformation,[],[f25])).
% 0.23/0.56  fof(f124,plain,(
% 0.23/0.56    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.23/0.56    inference(subsumption_resolution,[],[f123,f98])).
% 0.23/0.56  fof(f123,plain,(
% 0.23/0.56    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,sK2)),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f122])).
% 0.23/0.56  fof(f122,plain,(
% 0.23/0.56    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f109,f108])).
% 0.23/0.56  fof(f108,plain,(
% 0.23/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(resolution,[],[f107,f68])).
% 0.23/0.56  fof(f109,plain,(
% 0.23/0.56    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | v1_funct_2(sK3,sK0,sK2)),
% 0.23/0.56    inference(resolution,[],[f107,f63])).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  fof(f112,plain,(
% 0.23/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(resolution,[],[f107,f54])).
% 0.23/0.56  fof(f54,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.56  fof(f149,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f146,f71])).
% 0.23/0.56  fof(f146,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f137])).
% 0.23/0.56  fof(f137,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f107,f128])).
% 0.23/0.56  fof(f280,plain,(
% 0.23/0.56    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f279])).
% 0.23/0.56  fof(f279,plain,(
% 0.23/0.56    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f147,f153])).
% 0.23/0.56  fof(f147,plain,(
% 0.23/0.56    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f132,f71])).
% 0.23/0.56  fof(f132,plain,(
% 0.23/0.56    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f80,f128])).
% 0.23/0.56  fof(f348,plain,(
% 0.23/0.56    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.23/0.56    inference(subsumption_resolution,[],[f341,f39])).
% 0.23/0.56  fof(f341,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.23/0.56    inference(resolution,[],[f301,f79])).
% 0.23/0.56  fof(f79,plain,(
% 0.23/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.23/0.56    inference(equality_resolution,[],[f78])).
% 0.23/0.56  fof(f78,plain,(
% 0.23/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.23/0.56    inference(equality_resolution,[],[f59])).
% 0.23/0.56  fof(f59,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  fof(f301,plain,(
% 0.23/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f299])).
% 0.23/0.56  fof(f299,plain,(
% 0.23/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(superposition,[],[f244,f153])).
% 0.23/0.56  fof(f244,plain,(
% 0.23/0.56    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f241,f51])).
% 0.23/0.56  fof(f51,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.56  fof(f241,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f226])).
% 0.23/0.56  fof(f226,plain,(
% 0.23/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1) )),
% 0.23/0.56    inference(superposition,[],[f103,f148])).
% 0.23/0.56  fof(f148,plain,(
% 0.23/0.56    k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(subsumption_resolution,[],[f135,f51])).
% 0.23/0.56  fof(f135,plain,(
% 0.23/0.56    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f93,f128])).
% 0.23/0.56  fof(f93,plain,(
% 0.23/0.56    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 0.23/0.56    inference(resolution,[],[f88,f49])).
% 0.23/0.56  fof(f49,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f4])).
% 0.23/0.56  fof(f422,plain,(
% 0.23/0.56    sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.56    inference(subsumption_resolution,[],[f421,f51])).
% 0.23/0.56  fof(f421,plain,(
% 0.23/0.56    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.56    inference(forward_demodulation,[],[f361,f72])).
% 0.23/0.56  fof(f361,plain,(
% 0.23/0.56    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.56    inference(backward_demodulation,[],[f95,f353])).
% 0.23/0.56  fof(f95,plain,(
% 0.23/0.56    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.56    inference(resolution,[],[f87,f49])).
% 0.23/0.56  fof(f87,plain,(
% 0.23/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.23/0.56    inference(resolution,[],[f42,f54])).
% 0.23/0.56  fof(f419,plain,(
% 0.23/0.56    ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.23/0.56    inference(subsumption_resolution,[],[f418,f416])).
% 0.23/0.56  fof(f416,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.56    inference(forward_demodulation,[],[f355,f72])).
% 0.23/0.56  fof(f355,plain,(
% 0.23/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.23/0.56    inference(backward_demodulation,[],[f42,f353])).
% 0.23/0.56  fof(f418,plain,(
% 0.23/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.23/0.56    inference(forward_demodulation,[],[f417,f72])).
% 0.23/0.56  fof(f417,plain,(
% 0.23/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.23/0.56    inference(forward_demodulation,[],[f356,f353])).
% 0.23/0.56  fof(f356,plain,(
% 0.23/0.56    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.56    inference(backward_demodulation,[],[f80,f353])).
% 0.23/0.56  fof(f552,plain,(
% 0.23/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 0.23/0.56    inference(subsumption_resolution,[],[f545,f550])).
% 0.23/0.56  fof(f550,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k1_relset_1(X0,sK2,k1_xboole_0)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f542,f514])).
% 0.23/0.56  fof(f514,plain,(
% 0.23/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.56    inference(subsumption_resolution,[],[f513,f443])).
% 0.23/0.56  fof(f443,plain,(
% 0.23/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.56    inference(backward_demodulation,[],[f416,f424])).
% 0.23/0.56  fof(f513,plain,(
% 0.23/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.56    inference(forward_demodulation,[],[f512,f72])).
% 0.23/0.56  fof(f512,plain,(
% 0.23/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.23/0.56    inference(forward_demodulation,[],[f510,f441])).
% 0.23/0.56  fof(f441,plain,(
% 0.23/0.56    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)),
% 0.23/0.56    inference(backward_demodulation,[],[f358,f424])).
% 0.23/0.56  fof(f358,plain,(
% 0.23/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.23/0.56    inference(backward_demodulation,[],[f83,f353])).
% 0.23/0.56  fof(f510,plain,(
% 0.23/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.23/0.56    inference(resolution,[],[f439,f75])).
% 0.23/0.56  fof(f75,plain,(
% 0.23/0.56    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.23/0.56    inference(equality_resolution,[],[f62])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  fof(f439,plain,(
% 0.23/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.23/0.56    inference(backward_demodulation,[],[f354,f424])).
% 0.23/0.56  fof(f354,plain,(
% 0.23/0.56    v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.23/0.56    inference(backward_demodulation,[],[f41,f353])).
% 0.23/0.56  fof(f542,plain,(
% 0.23/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,sK2,k1_xboole_0)) )),
% 0.23/0.56    inference(resolution,[],[f537,f68])).
% 0.23/0.56  fof(f537,plain,(
% 0.23/0.56    ( ! [X3] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,sK2)))) )),
% 0.23/0.56    inference(resolution,[],[f525,f426])).
% 0.23/0.56  fof(f426,plain,(
% 0.23/0.56    r1_tarski(k2_relat_1(k1_xboole_0),sK2)),
% 0.23/0.56    inference(backward_demodulation,[],[f88,f424])).
% 0.23/0.56  fof(f525,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f524,f427])).
% 0.23/0.56  fof(f427,plain,(
% 0.23/0.56    v1_relat_1(k1_xboole_0)),
% 0.23/0.56    inference(backward_demodulation,[],[f89,f424])).
% 0.23/0.56  fof(f524,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f523,f51])).
% 0.23/0.56  fof(f523,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.56    inference(superposition,[],[f52,f514])).
% 0.23/0.56  fof(f545,plain,(
% 0.23/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 0.23/0.56    inference(resolution,[],[f537,f76])).
% 0.23/0.56  fof(f76,plain,(
% 0.23/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f61])).
% 0.23/0.56  fof(f61,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f32])).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (20287)------------------------------
% 0.23/0.56  % (20287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (20287)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (20287)Memory used [KB]: 6268
% 0.23/0.56  % (20287)Time elapsed: 0.150 s
% 0.23/0.56  % (20287)------------------------------
% 0.23/0.56  % (20287)------------------------------
% 0.23/0.56  % (20281)Success in time 0.19 s
%------------------------------------------------------------------------------
