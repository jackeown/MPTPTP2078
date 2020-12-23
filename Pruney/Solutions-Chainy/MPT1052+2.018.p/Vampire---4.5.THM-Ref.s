%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 (1454 expanded)
%              Number of leaves         :   19 ( 319 expanded)
%              Depth                    :   26
%              Number of atoms          :  303 (4161 expanded)
%              Number of equality atoms :  135 (1424 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f486,f453])).

fof(f453,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f445,f435])).

fof(f435,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f429,f127])).

fof(f127,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f125,f39])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f124,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f124,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f123,f101])).

fof(f101,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f53,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f90,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f45,f53])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f123,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f47,f42])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f429,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f425,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f92,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f54,f50])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_relat_1(k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f46,f53])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f425,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f238,f417])).

fof(f417,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f416,f380])).

fof(f380,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f379])).

fof(f379,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f283,f362])).

fof(f362,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f361,f237])).

fof(f237,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f234,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f234,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f73,f71])).

fof(f71,plain,(
    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(f40,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f63,f56])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f361,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f358,f191])).

% (1937)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f191,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f74,f71])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f56])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

% (1934)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f358,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f70,f234])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(ennf_transformation,[],[f15])).

% (1914)Refutation not found, incomplete strategy% (1914)------------------------------
% (1914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f15,axiom,(
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

% (1914)Termination reason: Refutation not found, incomplete strategy

% (1914)Memory used [KB]: 10746
% (1914)Time elapsed: 0.127 s
% (1914)------------------------------
% (1914)------------------------------
fof(f283,plain,
    ( sK0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f280,f38])).

fof(f38,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK0 != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f280,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f275,f238])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1))
      | r1_tarski(k2_relat_1(sK2),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f164,f39])).

fof(f164,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(X8,k2_zfmisc_1(X6,X7))
      | r1_tarski(k2_relat_1(X8),X7)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(subsumption_resolution,[],[f162,f53])).

fof(f162,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k2_relat_1(X8),X7)
      | ~ v1_relat_1(k2_zfmisc_1(X6,X7))
      | ~ r1_tarski(X8,k2_zfmisc_1(X6,X7))
      | ~ v1_relat_1(X8)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(superposition,[],[f48,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f416,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f415,f42])).

fof(f415,plain,
    ( k1_relat_1(k1_xboole_0) != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f414,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f414,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_relat_1(k1_xboole_0) != sK0
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f385,f43])).

fof(f43,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f385,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | k1_relat_1(k1_xboole_0) != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f38,f381])).

fof(f381,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f374,f380])).

fof(f374,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f89,f362])).

fof(f89,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f45,f39])).

fof(f238,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f234,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f445,plain,(
    sK0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f441,f44])).

fof(f441,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f418,f434])).

fof(f434,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f429,f137])).

fof(f137,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f135,f39])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f134,f50])).

fof(f134,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f133,f101])).

fof(f133,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f43])).

fof(f418,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | sK0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f38,f417])).

fof(f486,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f485,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f485,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f420,f170])).

fof(f170,plain,(
    ! [X2] :
      ( k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f168,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f168,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0)) ) ),
    inference(resolution,[],[f166,f49])).

fof(f166,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f72,f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f420,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f87,f417])).

fof(f87,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(resolution,[],[f71,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (1935)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (1927)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (1918)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (1914)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1912)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1935)Refutation not found, incomplete strategy% (1935)------------------------------
% 0.21/0.52  % (1935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1935)Memory used [KB]: 10874
% 0.21/0.52  % (1935)Time elapsed: 0.070 s
% 0.21/0.52  % (1935)------------------------------
% 0.21/0.52  % (1935)------------------------------
% 0.21/0.53  % (1917)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1933)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (1918)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (1915)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f487,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f486,f453])).
% 0.21/0.53  fof(f453,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(backward_demodulation,[],[f445,f435])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f429,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f125,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f20])).
% 0.21/0.53  fof(f20,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f19])).
% 0.21/0.53  fof(f19,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f124,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f53,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f90,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f55,f50])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f45,f53])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(superposition,[],[f47,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.53    inference(forward_demodulation,[],[f425,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f92,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.53    inference(resolution,[],[f54,f50])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_relat_1(k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f46,f53])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 0.21/0.53    inference(backward_demodulation,[],[f238,f417])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(subsumption_resolution,[],[f416,f380])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f379])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f372])).
% 0.21/0.53  fof(f372,plain,(
% 0.21/0.53    sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.53    inference(superposition,[],[f283,f362])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(superposition,[],[f361,f237])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f234,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(resolution,[],[f73,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f63,f56])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f358,f191])).
% 0.21/0.54  % (1937)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f74,f71])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f62,f56])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  % (1934)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f70,f234])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  % (1914)Refutation not found, incomplete strategy% (1914)------------------------------
% 0.21/0.54  % (1914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  % (1914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1914)Memory used [KB]: 10746
% 0.21/0.54  % (1914)Time elapsed: 0.127 s
% 0.21/0.54  % (1914)------------------------------
% 0.21/0.54  % (1914)------------------------------
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    sK0 != k1_relat_1(sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(resolution,[],[f280,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(resolution,[],[f275,f238])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(sK2,k2_zfmisc_1(X0,X1)) | r1_tarski(k2_relat_1(sK2),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(resolution,[],[f164,f39])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (~v1_relat_1(X8) | ~r1_tarski(X8,k2_zfmisc_1(X6,X7)) | r1_tarski(k2_relat_1(X8),X7) | k1_xboole_0 = X7 | k1_xboole_0 = X6) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f53])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tarski(k2_relat_1(X8),X7) | ~v1_relat_1(k2_zfmisc_1(X6,X7)) | ~r1_tarski(X8,k2_zfmisc_1(X6,X7)) | ~v1_relat_1(X8) | k1_xboole_0 = X7 | k1_xboole_0 = X6) )),
% 0.21/0.54    inference(superposition,[],[f48,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f416,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(forward_demodulation,[],[f415,f42])).
% 0.21/0.54  fof(f415,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) != sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f414,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f414,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,sK1) | k1_relat_1(k1_xboole_0) != sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(forward_demodulation,[],[f385,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k1_xboole_0),sK1) | k1_relat_1(k1_xboole_0) != sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(superposition,[],[f38,f381])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f374,f380])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(superposition,[],[f89,f362])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f45,f39])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f234,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    sK0 != k1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f441,f44])).
% 0.21/0.54  fof(f441,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | sK0 != k1_relat_1(sK2)),
% 0.21/0.54    inference(backward_demodulation,[],[f418,f434])).
% 0.21/0.54  fof(f434,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f429,f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ~r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f135,f39])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f134,f50])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f133,f101])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f48,f43])).
% 0.21/0.54  fof(f418,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | sK0 != k1_relat_1(sK2)),
% 0.21/0.54    inference(backward_demodulation,[],[f38,f417])).
% 0.21/0.54  fof(f486,plain,(
% 0.21/0.54    k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f485,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f485,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(superposition,[],[f420,f170])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X2] : (k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0)) | k1_xboole_0 = X2) )),
% 0.21/0.54    inference(resolution,[],[f168,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ( ! [X2] : (v1_xboole_0(X2) | k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0))) )),
% 0.21/0.54    inference(resolution,[],[f166,f49])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f72,f41])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f57,f56])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.21/0.54  fof(f420,plain,(
% 0.21/0.54    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f87,f417])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ~v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 0.21/0.54    inference(resolution,[],[f71,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (1918)------------------------------
% 0.21/0.54  % (1918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1918)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (1918)Memory used [KB]: 6396
% 0.21/0.54  % (1918)Time elapsed: 0.084 s
% 0.21/0.54  % (1918)------------------------------
% 0.21/0.54  % (1918)------------------------------
% 0.21/0.54  % (1934)Refutation not found, incomplete strategy% (1934)------------------------------
% 0.21/0.54  % (1934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1934)Memory used [KB]: 1791
% 0.21/0.54  % (1934)Time elapsed: 0.139 s
% 0.21/0.54  % (1934)------------------------------
% 0.21/0.54  % (1934)------------------------------
% 0.21/0.54  % (1910)Success in time 0.177 s
%------------------------------------------------------------------------------
