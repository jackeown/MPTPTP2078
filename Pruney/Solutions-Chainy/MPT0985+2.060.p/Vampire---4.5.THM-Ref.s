%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  147 (2384 expanded)
%              Number of leaves         :   19 ( 480 expanded)
%              Depth                    :   27
%              Number of atoms          :  330 (10210 expanded)
%              Number of equality atoms :   90 (1711 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1180,f614])).

fof(f614,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f612,f561])).

fof(f561,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f559,f170])).

fof(f170,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f139,f169])).

fof(f169,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f165,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f165,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f162,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f108,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f162,plain,(
    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f161,f134])).

fof(f134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f126,f112])).

fof(f112,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f109,f58])).

fof(f109,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f108,f98])).

fof(f98,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f55,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f126,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f161,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f159,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

% (3896)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f159,plain,(
    v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f151,f112])).

fof(f151,plain,(
    ! [X0] : v5_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f139,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f137,f121])).

fof(f121,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f85,f112])).

fof(f85,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f53,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f137,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f559,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f478,f116])).

fof(f116,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f98,f112])).

fof(f478,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f76,f87])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f612,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f94,f116])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f89,f87])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f1180,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1179,f121])).

fof(f1179,plain,(
    ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1178,f1024])).

fof(f1024,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1010,f58])).

fof(f1010,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f997,f110])).

fof(f997,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f975,f86])).

fof(f975,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f100,f971])).

fof(f971,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f324,f328,f962,f964])).

fof(f964,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f496,f956])).

fof(f956,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f955,f472])).

fof(f472,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f955,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f949,f48])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f949,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f496,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f402,f488])).

fof(f488,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f481,f51])).

fof(f51,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f481,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f77,f49])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f402,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f401,f131])).

fof(f131,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f125,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f49])).

fof(f401,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f400,f130])).

fof(f130,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f125,f57])).

fof(f400,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(subsumption_resolution,[],[f397,f330])).

fof(f330,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f329,f125])).

fof(f329,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f326,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f326,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f62,f321])).

fof(f321,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f320,f125])).

fof(f320,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f319,f47])).

fof(f319,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f397,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(resolution,[],[f61,f328])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f962,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f492,f956])).

fof(f492,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f334,f488])).

fof(f334,plain,(
    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f333,f131])).

fof(f333,plain,(
    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f332,f130])).

fof(f332,plain,(
    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f331,f330])).

fof(f331,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    inference(resolution,[],[f328,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f328,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f327,f125])).

fof(f327,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f325,f47])).

fof(f325,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f63,f321])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f324,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f323,f321])).

fof(f323,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f322,f321])).

fof(f322,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f46,f321])).

fof(f46,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f100,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f71,f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1178,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1177,f116])).

fof(f1177,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1066,f121])).

fof(f1066,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f1000,f1024])).

fof(f1000,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f999,f971])).

fof(f999,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f998,f87])).

fof(f998,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f977,f328])).

fof(f977,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f324,f971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3890)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (3905)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (3897)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (3906)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (3889)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3898)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3905)Refutation not found, incomplete strategy% (3905)------------------------------
% 0.21/0.53  % (3905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3886)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3905)Memory used [KB]: 10874
% 0.21/0.53  % (3905)Time elapsed: 0.067 s
% 0.21/0.53  % (3905)------------------------------
% 0.21/0.53  % (3905)------------------------------
% 0.21/0.53  % (3887)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3892)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (3908)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (3900)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3900)Refutation not found, incomplete strategy% (3900)------------------------------
% 0.21/0.54  % (3900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3885)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3900)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3900)Memory used [KB]: 10618
% 0.21/0.54  % (3900)Time elapsed: 0.120 s
% 0.21/0.54  % (3900)------------------------------
% 0.21/0.54  % (3900)------------------------------
% 0.21/0.54  % (3894)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3888)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (3912)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (3910)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (3909)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3911)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (3904)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (3889)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (3901)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (3902)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.56  % (3903)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f1181,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(subsumption_resolution,[],[f1180,f614])).
% 1.47/0.56  fof(f614,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f612,f561])).
% 1.47/0.56  fof(f561,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.47/0.56    inference(forward_demodulation,[],[f559,f170])).
% 1.47/0.56  fof(f170,plain,(
% 1.47/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(backward_demodulation,[],[f139,f169])).
% 1.47/0.56  fof(f169,plain,(
% 1.47/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(resolution,[],[f165,f58])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.47/0.56  fof(f165,plain,(
% 1.47/0.56    v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 1.47/0.56    inference(resolution,[],[f162,f110])).
% 1.47/0.56  fof(f110,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.47/0.56    inference(resolution,[],[f108,f70])).
% 1.47/0.56  fof(f70,plain,(
% 1.47/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.47/0.56    inference(resolution,[],[f59,f52])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    v1_xboole_0(k1_xboole_0)),
% 1.47/0.56    inference(cnf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    v1_xboole_0(k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f29])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.47/0.56  fof(f162,plain,(
% 1.47/0.56    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.47/0.56    inference(subsumption_resolution,[],[f161,f134])).
% 1.47/0.56  fof(f134,plain,(
% 1.47/0.56    v1_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(superposition,[],[f126,f112])).
% 1.47/0.56  fof(f112,plain,(
% 1.47/0.56    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.47/0.56    inference(resolution,[],[f109,f58])).
% 1.47/0.56  fof(f109,plain,(
% 1.47/0.56    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.47/0.56    inference(resolution,[],[f108,f98])).
% 1.47/0.56  fof(f98,plain,(
% 1.47/0.56    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.56    inference(superposition,[],[f55,f86])).
% 1.47/0.56  fof(f86,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.47/0.56    inference(equality_resolution,[],[f74])).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.47/0.56    inference(pure_predicate_removal,[],[f18])).
% 1.47/0.56  fof(f18,axiom,(
% 1.47/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.47/0.56  fof(f126,plain,(
% 1.47/0.56    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.47/0.56    inference(resolution,[],[f75,f55])).
% 1.47/0.56  fof(f75,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f40])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.56  fof(f161,plain,(
% 1.47/0.56    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(resolution,[],[f159,f68])).
% 1.47/0.56  fof(f68,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f38])).
% 1.47/0.56  % (3896)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.47/0.56  fof(f159,plain,(
% 1.47/0.56    v5_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.47/0.56    inference(superposition,[],[f151,f112])).
% 1.47/0.56  fof(f151,plain,(
% 1.47/0.56    ( ! [X0] : (v5_relat_1(k6_partfun1(X0),X0)) )),
% 1.47/0.56    inference(resolution,[],[f78,f55])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.47/0.56    inference(pure_predicate_removal,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.47/0.56  fof(f139,plain,(
% 1.47/0.56    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(forward_demodulation,[],[f137,f121])).
% 1.47/0.56  fof(f121,plain,(
% 1.47/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(superposition,[],[f85,f112])).
% 1.47/0.56  fof(f85,plain,(
% 1.47/0.56    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f54,f53,f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,axiom,(
% 1.47/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.47/0.56  fof(f137,plain,(
% 1.47/0.56    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.47/0.56    inference(resolution,[],[f134,f57])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.47/0.56  fof(f559,plain,(
% 1.47/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.47/0.56    inference(resolution,[],[f478,f116])).
% 1.47/0.56  fof(f116,plain,(
% 1.47/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.56    inference(backward_demodulation,[],[f98,f112])).
% 1.47/0.56  fof(f478,plain,(
% 1.47/0.56    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 1.47/0.56    inference(superposition,[],[f76,f87])).
% 1.47/0.56  fof(f87,plain,(
% 1.47/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.47/0.56    inference(equality_resolution,[],[f73])).
% 1.47/0.56  fof(f73,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f3])).
% 1.47/0.56  fof(f76,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.47/0.56  fof(f612,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.47/0.56    inference(resolution,[],[f94,f116])).
% 1.47/0.56  fof(f94,plain,(
% 1.47/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.47/0.56    inference(forward_demodulation,[],[f89,f87])).
% 1.47/0.56  fof(f89,plain,(
% 1.47/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.47/0.56    inference(equality_resolution,[],[f81])).
% 1.47/0.56  fof(f81,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(flattening,[],[f44])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.47/0.56  fof(f1180,plain,(
% 1.47/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f1179,f121])).
% 1.47/0.56  fof(f1179,plain,(
% 1.47/0.56    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f1178,f1024])).
% 1.47/0.56  fof(f1024,plain,(
% 1.47/0.56    k1_xboole_0 = sK2),
% 1.47/0.56    inference(resolution,[],[f1010,f58])).
% 1.47/0.56  fof(f1010,plain,(
% 1.47/0.56    v1_xboole_0(sK2)),
% 1.47/0.56    inference(resolution,[],[f997,f110])).
% 1.47/0.56  fof(f997,plain,(
% 1.47/0.56    r1_tarski(sK2,k1_xboole_0)),
% 1.47/0.56    inference(forward_demodulation,[],[f975,f86])).
% 1.47/0.56  fof(f975,plain,(
% 1.47/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.47/0.56    inference(backward_demodulation,[],[f100,f971])).
% 1.47/0.56  fof(f971,plain,(
% 1.47/0.56    k1_xboole_0 = sK1),
% 1.47/0.56    inference(global_subsumption,[],[f324,f328,f962,f964])).
% 1.47/0.56  fof(f964,plain,(
% 1.47/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 1.47/0.56    inference(superposition,[],[f496,f956])).
% 1.47/0.56  fof(f956,plain,(
% 1.47/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.47/0.56    inference(superposition,[],[f955,f472])).
% 1.47/0.56  fof(f472,plain,(
% 1.47/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.47/0.56    inference(resolution,[],[f76,f49])).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.56    inference(flattening,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f22])).
% 1.47/0.56  fof(f22,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.47/0.56    inference(negated_conjecture,[],[f21])).
% 1.47/0.56  fof(f21,conjecture,(
% 1.47/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.47/0.56  fof(f955,plain,(
% 1.47/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.47/0.56    inference(subsumption_resolution,[],[f949,f48])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f949,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.56    inference(resolution,[],[f84,f49])).
% 1.47/0.56  fof(f84,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f496,plain,(
% 1.47/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.47/0.56    inference(backward_demodulation,[],[f402,f488])).
% 1.47/0.56  fof(f488,plain,(
% 1.47/0.56    sK1 = k2_relat_1(sK2)),
% 1.47/0.56    inference(forward_demodulation,[],[f481,f51])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f481,plain,(
% 1.47/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.47/0.56    inference(resolution,[],[f77,f49])).
% 1.47/0.56  fof(f77,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.47/0.56  fof(f402,plain,(
% 1.47/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.47/0.56    inference(forward_demodulation,[],[f401,f131])).
% 1.47/0.56  fof(f131,plain,(
% 1.47/0.56    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 1.47/0.56    inference(resolution,[],[f125,f56])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f27])).
% 1.47/0.56  fof(f125,plain,(
% 1.47/0.56    v1_relat_1(sK2)),
% 1.47/0.56    inference(resolution,[],[f75,f49])).
% 1.47/0.56  fof(f401,plain,(
% 1.47/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))),
% 1.47/0.56    inference(forward_demodulation,[],[f400,f130])).
% 1.47/0.56  fof(f130,plain,(
% 1.47/0.56    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 1.47/0.56    inference(resolution,[],[f125,f57])).
% 1.47/0.56  fof(f400,plain,(
% 1.47/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 1.47/0.56    inference(subsumption_resolution,[],[f397,f330])).
% 1.47/0.56  fof(f330,plain,(
% 1.47/0.56    v1_relat_1(k4_relat_1(sK2))),
% 1.47/0.56    inference(subsumption_resolution,[],[f329,f125])).
% 1.47/0.56  fof(f329,plain,(
% 1.47/0.56    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.47/0.56    inference(subsumption_resolution,[],[f326,f47])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    v1_funct_1(sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f326,plain,(
% 1.47/0.56    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.47/0.56    inference(superposition,[],[f62,f321])).
% 1.47/0.56  fof(f321,plain,(
% 1.47/0.56    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.47/0.56    inference(subsumption_resolution,[],[f320,f125])).
% 1.47/0.56  fof(f320,plain,(
% 1.47/0.56    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.47/0.56    inference(subsumption_resolution,[],[f319,f47])).
% 1.47/0.56  fof(f319,plain,(
% 1.47/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.47/0.56    inference(resolution,[],[f64,f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    v2_funct_1(sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(flattening,[],[f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(flattening,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.47/0.56  fof(f397,plain,(
% 1.47/0.56    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 1.47/0.56    inference(resolution,[],[f61,f328])).
% 1.47/0.56  fof(f61,plain,(
% 1.47/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(flattening,[],[f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f20])).
% 1.47/0.56  fof(f20,axiom,(
% 1.47/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.47/0.56  fof(f962,plain,(
% 1.47/0.56    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 1.47/0.56    inference(superposition,[],[f492,f956])).
% 1.47/0.56  fof(f492,plain,(
% 1.47/0.56    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 1.47/0.56    inference(backward_demodulation,[],[f334,f488])).
% 1.47/0.56  fof(f334,plain,(
% 1.47/0.56    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.47/0.56    inference(forward_demodulation,[],[f333,f131])).
% 1.47/0.56  fof(f333,plain,(
% 1.47/0.56    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))),
% 1.47/0.56    inference(forward_demodulation,[],[f332,f130])).
% 1.47/0.56  fof(f332,plain,(
% 1.47/0.56    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 1.47/0.56    inference(subsumption_resolution,[],[f331,f330])).
% 1.47/0.56  fof(f331,plain,(
% 1.47/0.56    ~v1_relat_1(k4_relat_1(sK2)) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 1.47/0.56    inference(resolution,[],[f328,f60])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f31])).
% 1.47/0.56  fof(f328,plain,(
% 1.47/0.56    v1_funct_1(k4_relat_1(sK2))),
% 1.47/0.56    inference(subsumption_resolution,[],[f327,f125])).
% 1.47/0.56  fof(f327,plain,(
% 1.47/0.56    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.47/0.56    inference(subsumption_resolution,[],[f325,f47])).
% 1.47/0.56  fof(f325,plain,(
% 1.47/0.56    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.47/0.56    inference(superposition,[],[f63,f321])).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f324,plain,(
% 1.47/0.56    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.56    inference(forward_demodulation,[],[f323,f321])).
% 1.47/0.56  fof(f323,plain,(
% 1.47/0.56    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f322,f321])).
% 1.47/0.56  fof(f322,plain,(
% 1.47/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.47/0.56    inference(backward_demodulation,[],[f46,f321])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f100,plain,(
% 1.47/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.47/0.56    inference(resolution,[],[f71,f49])).
% 1.47/0.56  fof(f71,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f5])).
% 1.47/0.56  fof(f1178,plain,(
% 1.47/0.56    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 1.47/0.56    inference(subsumption_resolution,[],[f1177,f116])).
% 1.47/0.56  fof(f1177,plain,(
% 1.47/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f1066,f121])).
% 1.47/0.56  fof(f1066,plain,(
% 1.47/0.56    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 1.47/0.56    inference(backward_demodulation,[],[f1000,f1024])).
% 1.47/0.56  fof(f1000,plain,(
% 1.47/0.56    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.56    inference(forward_demodulation,[],[f999,f971])).
% 1.47/0.56  fof(f999,plain,(
% 1.47/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f998,f87])).
% 1.47/0.56  fof(f998,plain,(
% 1.47/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.47/0.56    inference(subsumption_resolution,[],[f977,f328])).
% 1.47/0.56  fof(f977,plain,(
% 1.47/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2))),
% 1.47/0.56    inference(backward_demodulation,[],[f324,f971])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (3889)------------------------------
% 1.47/0.56  % (3889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (3889)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (3889)Memory used [KB]: 6780
% 1.47/0.56  % (3889)Time elapsed: 0.090 s
% 1.47/0.56  % (3889)------------------------------
% 1.47/0.56  % (3889)------------------------------
% 1.47/0.56  % (3893)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.56  % (3891)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.57  % (3882)Success in time 0.196 s
%------------------------------------------------------------------------------
