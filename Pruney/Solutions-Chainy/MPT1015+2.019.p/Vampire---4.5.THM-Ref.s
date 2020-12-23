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
% DateTime   : Thu Dec  3 13:05:28 EST 2020

% Result     : Theorem 4.58s
% Output     : Refutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  242 (23154 expanded)
%              Number of leaves         :   30 (7209 expanded)
%              Depth                    :   35
%              Number of atoms          :  791 (178149 expanded)
%              Number of equality atoms :  254 (5159 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5726,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5550,f5542])).

fof(f5542,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f3031,f5488])).

fof(f5488,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f3361,f3709])).

fof(f3709,plain,(
    k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1253,f3334])).

fof(f3334,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f3073])).

fof(f3073,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f485,f3020])).

fof(f3020,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f2949,f173])).

fof(f173,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f125,f79])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f70,f69])).

fof(f69,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & v2_funct_1(sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & v2_funct_1(sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f2949,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f126,f2695])).

fof(f2695,plain,
    ( sK2 = k6_relat_1(sK0)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f2682,f443])).

fof(f443,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f440,f132])).

fof(f132,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f130,f100])).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f130,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f92,f79])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f440,plain,
    ( sK2 = k5_relat_1(sK2,k6_relat_1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f312,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f312,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f311,f132])).

fof(f311,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f164,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f164,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f110,f79])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2682,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k6_relat_1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f2585])).

fof(f2585,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f1504,f2566])).

fof(f2566,plain,
    ( k6_relat_1(sK0) = k2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f2523])).

fof(f2523,plain,
    ( k6_relat_1(sK0) = k2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f2362,f1501])).

fof(f1501,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1408,f1308])).

fof(f1308,plain,
    ( ~ v2_funct_1(sK2)
    | sK0 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f178,f1307])).

fof(f1307,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f1266,f219])).

fof(f219,plain,(
    sK0 = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f143,f218])).

fof(f218,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f190,f217])).

fof(f217,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f216,f74])).

fof(f74,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f216,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f214,f76])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f214,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f105,f75])).

fof(f75,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f190,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f108,f76])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f143,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f131,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f131,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f129,f100])).

fof(f129,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f92,f76])).

fof(f1266,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f573,f1253])).

fof(f573,plain,(
    k2_relat_1(sK2) = k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(backward_demodulation,[],[f442,f564])).

fof(f564,plain,(
    k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f188,f132])).

fof(f188,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k2_relat_1(k5_relat_1(X5,sK1)) = k9_relat_1(sK1,k2_relat_1(X5)) ) ),
    inference(resolution,[],[f91,f131])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f442,plain,(
    k2_relat_1(sK2) = k10_relat_1(sK1,k9_relat_1(sK1,k2_relat_1(sK2))) ),
    inference(resolution,[],[f312,f223])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f212,f218])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f211,f131])).

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f209,f81])).

fof(f81,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f209,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK1)
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f106,f74])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f178,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f175,f132])).

fof(f175,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f96,f77])).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1408,plain,
    ( v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f1271,f81])).

fof(f1271,plain,
    ( ~ v2_funct_1(sK1)
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f933,f1253])).

fof(f933,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f427,f931])).

fof(f931,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f647,f76])).

fof(f647,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK1) = k1_partfun1(sK0,sK0,X0,X1,sK2,sK1) ) ),
    inference(resolution,[],[f417,f79])).

fof(f417,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k5_relat_1(sK2,sK1) = k1_partfun1(X4,X5,X6,X7,sK2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f277,f77])).

fof(f277,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f120,f74])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f427,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f426,f77])).

fof(f426,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f425,f79])).

fof(f425,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f302,f78])).

fof(f78,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,sK0)
      | ~ v2_funct_1(k1_partfun1(X0,sK0,sK0,sK0,X1,sK1))
      | v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f301,f74])).

fof(f301,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(k1_partfun1(X0,sK0,sK0,sK0,X1,sK1))
      | v2_funct_1(X1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_2(X1,X0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f299,f76])).

fof(f299,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(k1_partfun1(X0,sK0,sK0,sK0,X1,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v2_funct_1(X1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_2(X1,X0,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f116,f75])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f2362,plain,
    ( k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f2361,f1501])).

fof(f2361,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f2360,f220])).

fof(f220,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f182,f218])).

fof(f182,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f181,f131])).

fof(f181,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f179,f81])).

fof(f179,plain,
    ( ~ v2_funct_1(sK1)
    | k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f97,f74])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2360,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f2359,f1509])).

fof(f1509,plain,
    ( k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1262,f1408])).

fof(f1262,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f365,f1253])).

fof(f365,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f360,f132])).

fof(f360,plain,
    ( k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f236,f77])).

fof(f236,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f235,f131])).

fof(f235,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f233,f81])).

fof(f233,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f98,f74])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f2359,plain,
    ( k2_funct_1(sK1) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f2340,f147])).

fof(f147,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f146,f131])).

fof(f146,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f144,f81])).

fof(f144,plain,
    ( ~ v2_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f74])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f2340,plain,
    ( k2_funct_1(sK1) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f1584,f152])).

fof(f152,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f151,f131])).

fof(f151,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f149,f81])).

fof(f149,plain,
    ( ~ v2_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f94,f74])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1584,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X1,k2_funct_1(sK2)) != X1
      | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
      | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
      | k1_xboole_0 = sK0
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f1547,f1491])).

fof(f1491,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1408,f148])).

fof(f148,plain,
    ( ~ v2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f145,f132])).

fof(f145,plain,
    ( ~ v2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f93,f77])).

fof(f1547,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | k5_relat_1(X1,k2_funct_1(sK2)) != X1
      | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
      | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f1492,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f1492,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1408,f153])).

fof(f153,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f150,f132])).

fof(f150,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f94,f77])).

fof(f1504,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f1503])).

fof(f1503,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f1408,f1354])).

fof(f1354,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f1317])).

fof(f1317,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f551,f1307])).

fof(f551,plain,
    ( ~ v2_funct_1(sK2)
    | sK0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f298,f548])).

fof(f548,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f168,f308])).

fof(f308,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f307,f132])).

fof(f307,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f162,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f162,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f109,f79])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f168,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f132,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f298,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | sK0 != k9_relat_1(sK2,sK0)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f297,f204])).

fof(f204,plain,(
    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f202,f193])).

fof(f193,plain,(
    ! [X1] : k9_relat_1(sK2,X1) = k7_relset_1(sK0,sK0,sK2,X1) ),
    inference(resolution,[],[f115,f79])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f202,plain,(
    k7_relset_1(sK0,sK0,sK2,sK0) = k2_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f111,f79])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f297,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f296,f77])).

fof(f296,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f292,f79])).

fof(f292,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | sK0 != k2_relset_1(sK0,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f128,f78])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f113,f83])).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f126,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f82,f83])).

fof(f82,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f485,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f142,f218])).

fof(f142,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f131,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1253,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f974,f936])).

fof(f936,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k5_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f934,f931])).

fof(f934,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f232,f931])).

fof(f232,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f231,f76])).

fof(f231,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f118,f80])).

fof(f80,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f974,plain,(
    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f973,f931])).

fof(f973,plain,(
    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f656,f76])).

fof(f656,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK0,X0,X1,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f433,f79])).

fof(f433,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(k1_partfun1(X4,X5,X6,X7,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X7)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f280,f77])).

fof(f280,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | m1_subset_1(k1_partfun1(X2,X3,X0,X1,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f122,f74])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f3361,plain,(
    sK2 = k5_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3065,f671])).

fof(f671,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f446])).

fof(f446,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(superposition,[],[f137,f86])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f137,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k6_relat_1(X0))
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(resolution,[],[f89,f84])).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f3065,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f443,f3020])).

fof(f3031,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f173,f3020])).

fof(f5550,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f3335,f5488])).

fof(f3335,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3025,f671])).

fof(f3025,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f126,f3020])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n006.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:28:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (13838)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.49  % (13846)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (13859)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (13851)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (13837)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (13861)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (13839)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (13847)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (13841)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (13835)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (13855)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (13842)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (13836)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (13834)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (13854)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (13844)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (13850)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (13856)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (13849)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.54  % (13848)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.54  % (13853)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.54  % (13845)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  % (13840)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (13852)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.55  % (13863)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (13843)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.55  % (13858)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.55  % (13862)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.55  % (13850)Refutation not found, incomplete strategy% (13850)------------------------------
% 1.42/0.55  % (13850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (13850)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (13850)Memory used [KB]: 10746
% 1.42/0.55  % (13850)Time elapsed: 0.148 s
% 1.42/0.55  % (13850)------------------------------
% 1.42/0.55  % (13850)------------------------------
% 1.42/0.56  % (13857)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.58/0.56  % (13860)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.35/0.72  % (13905)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.11/0.81  % (13836)Time limit reached!
% 3.11/0.81  % (13836)------------------------------
% 3.11/0.81  % (13836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.11/0.82  % (13836)Termination reason: Time limit
% 3.11/0.82  % (13836)Termination phase: Saturation
% 3.11/0.82  
% 3.11/0.82  % (13836)Memory used [KB]: 6780
% 3.11/0.82  % (13836)Time elapsed: 0.400 s
% 3.11/0.82  % (13836)------------------------------
% 3.11/0.82  % (13836)------------------------------
% 3.11/0.82  % (13858)Time limit reached!
% 3.11/0.82  % (13858)------------------------------
% 3.11/0.82  % (13858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.11/0.82  % (13858)Termination reason: Time limit
% 3.11/0.82  
% 3.11/0.82  % (13858)Memory used [KB]: 13048
% 3.11/0.82  % (13858)Time elapsed: 0.412 s
% 3.11/0.82  % (13858)------------------------------
% 3.11/0.82  % (13858)------------------------------
% 4.31/0.94  % (14022)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.31/0.94  % (13863)Time limit reached!
% 4.31/0.94  % (13863)------------------------------
% 4.31/0.94  % (13863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.94  % (13863)Termination reason: Time limit
% 4.31/0.94  
% 4.31/0.94  % (13863)Memory used [KB]: 4349
% 4.31/0.94  % (13863)Time elapsed: 0.525 s
% 4.31/0.94  % (13863)------------------------------
% 4.31/0.94  % (13863)------------------------------
% 4.31/0.95  % (13840)Time limit reached!
% 4.31/0.95  % (13840)------------------------------
% 4.31/0.95  % (13840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.95  % (13840)Termination reason: Time limit
% 4.31/0.95  % (13840)Termination phase: Saturation
% 4.31/0.95  
% 4.31/0.95  % (13840)Memory used [KB]: 15095
% 4.31/0.95  % (13840)Time elapsed: 0.500 s
% 4.31/0.95  % (13840)------------------------------
% 4.31/0.95  % (13840)------------------------------
% 4.31/0.96  % (14021)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.31/0.97  % (13848)Time limit reached!
% 4.31/0.97  % (13848)------------------------------
% 4.31/0.97  % (13848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/0.98  % (13841)Refutation found. Thanks to Tanya!
% 4.58/0.98  % SZS status Theorem for theBenchmark
% 4.58/0.99  % (13848)Termination reason: Time limit
% 4.58/0.99  % (13848)Termination phase: Saturation
% 4.58/0.99  
% 4.58/0.99  % (13848)Memory used [KB]: 6524
% 4.58/0.99  % (13848)Time elapsed: 0.500 s
% 4.58/0.99  % (13848)------------------------------
% 4.58/0.99  % (13848)------------------------------
% 4.58/0.99  % SZS output start Proof for theBenchmark
% 4.58/0.99  fof(f5726,plain,(
% 4.58/0.99    $false),
% 4.58/0.99    inference(subsumption_resolution,[],[f5550,f5542])).
% 4.58/0.99  fof(f5542,plain,(
% 4.58/0.99    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 4.58/0.99    inference(backward_demodulation,[],[f3031,f5488])).
% 4.58/0.99  fof(f5488,plain,(
% 4.58/0.99    k1_xboole_0 = sK2),
% 4.58/0.99    inference(backward_demodulation,[],[f3361,f3709])).
% 4.58/0.99  fof(f3709,plain,(
% 4.58/0.99    k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0)),
% 4.58/0.99    inference(backward_demodulation,[],[f1253,f3334])).
% 4.58/0.99  fof(f3334,plain,(
% 4.58/0.99    k1_xboole_0 = sK1),
% 4.58/0.99    inference(trivial_inequality_removal,[],[f3073])).
% 4.58/0.99  fof(f3073,plain,(
% 4.58/0.99    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 4.58/0.99    inference(backward_demodulation,[],[f485,f3020])).
% 4.58/0.99  fof(f3020,plain,(
% 4.58/0.99    k1_xboole_0 = sK0),
% 4.58/0.99    inference(subsumption_resolution,[],[f2949,f173])).
% 4.58/0.99  fof(f173,plain,(
% 4.58/0.99    r2_relset_1(sK0,sK0,sK2,sK2)),
% 4.58/0.99    inference(resolution,[],[f125,f79])).
% 4.58/0.99  fof(f79,plain,(
% 4.58/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f71,plain,(
% 4.58/0.99    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 4.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f70,f69])).
% 4.58/0.99  fof(f69,plain,(
% 4.58/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 4.58/0.99    introduced(choice_axiom,[])).
% 4.58/0.99  fof(f70,plain,(
% 4.58/0.99    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 4.58/0.99    introduced(choice_axiom,[])).
% 4.58/0.99  fof(f31,plain,(
% 4.58/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.58/0.99    inference(flattening,[],[f30])).
% 4.58/0.99  fof(f30,plain,(
% 4.58/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.58/0.99    inference(ennf_transformation,[],[f29])).
% 4.58/0.99  fof(f29,negated_conjecture,(
% 4.58/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 4.58/0.99    inference(negated_conjecture,[],[f28])).
% 4.58/0.99  fof(f28,conjecture,(
% 4.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 4.58/0.99  fof(f125,plain,(
% 4.58/0.99    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 4.58/0.99    inference(duplicate_literal_removal,[],[f124])).
% 4.58/0.99  fof(f124,plain,(
% 4.58/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.58/0.99    inference(equality_resolution,[],[f119])).
% 4.58/0.99  fof(f119,plain,(
% 4.58/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.58/0.99    inference(cnf_transformation,[],[f73])).
% 4.58/0.99  fof(f73,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.58/0.99    inference(nnf_transformation,[],[f64])).
% 4.58/0.99  fof(f64,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.58/0.99    inference(flattening,[],[f63])).
% 4.58/0.99  fof(f63,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.58/0.99    inference(ennf_transformation,[],[f20])).
% 4.58/0.99  fof(f20,axiom,(
% 4.58/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 4.58/0.99  fof(f2949,plain,(
% 4.58/0.99    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(superposition,[],[f126,f2695])).
% 4.58/0.99  fof(f2695,plain,(
% 4.58/0.99    sK2 = k6_relat_1(sK0) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(forward_demodulation,[],[f2682,f443])).
% 4.58/0.99  fof(f443,plain,(
% 4.58/0.99    sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 4.58/0.99    inference(subsumption_resolution,[],[f440,f132])).
% 4.58/0.99  fof(f132,plain,(
% 4.58/0.99    v1_relat_1(sK2)),
% 4.58/0.99    inference(subsumption_resolution,[],[f130,f100])).
% 4.58/0.99  fof(f100,plain,(
% 4.58/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.58/0.99    inference(cnf_transformation,[],[f3])).
% 4.58/0.99  fof(f3,axiom,(
% 4.58/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 4.58/0.99  fof(f130,plain,(
% 4.58/0.99    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 4.58/0.99    inference(resolution,[],[f92,f79])).
% 4.58/0.99  fof(f92,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f36])).
% 4.58/0.99  fof(f36,plain,(
% 4.58/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(ennf_transformation,[],[f1])).
% 4.58/0.99  fof(f1,axiom,(
% 4.58/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 4.58/0.99  fof(f440,plain,(
% 4.58/0.99    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f312,f102])).
% 4.58/0.99  fof(f102,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f47])).
% 4.58/0.99  fof(f47,plain,(
% 4.58/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(flattening,[],[f46])).
% 4.58/0.99  fof(f46,plain,(
% 4.58/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(ennf_transformation,[],[f10])).
% 4.58/0.99  fof(f10,axiom,(
% 4.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 4.58/0.99  fof(f312,plain,(
% 4.58/0.99    r1_tarski(k2_relat_1(sK2),sK0)),
% 4.58/0.99    inference(subsumption_resolution,[],[f311,f132])).
% 4.58/0.99  fof(f311,plain,(
% 4.58/0.99    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f164,f103])).
% 4.58/0.99  fof(f103,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f72])).
% 4.58/0.99  fof(f72,plain,(
% 4.58/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(nnf_transformation,[],[f48])).
% 4.58/0.99  fof(f48,plain,(
% 4.58/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(ennf_transformation,[],[f2])).
% 4.58/0.99  fof(f2,axiom,(
% 4.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 4.58/0.99  fof(f164,plain,(
% 4.58/0.99    v5_relat_1(sK2,sK0)),
% 4.58/0.99    inference(resolution,[],[f110,f79])).
% 4.58/0.99  fof(f110,plain,(
% 4.58/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f56])).
% 4.58/0.99  fof(f56,plain,(
% 4.58/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.58/0.99    inference(ennf_transformation,[],[f17])).
% 4.58/0.99  fof(f17,axiom,(
% 4.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 4.58/0.99  fof(f2682,plain,(
% 4.58/0.99    k6_relat_1(sK0) = k5_relat_1(sK2,k6_relat_1(sK0)) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(duplicate_literal_removal,[],[f2585])).
% 4.58/0.99  fof(f2585,plain,(
% 4.58/0.99    k6_relat_1(sK0) = k5_relat_1(sK2,k6_relat_1(sK0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 4.58/0.99    inference(superposition,[],[f1504,f2566])).
% 4.58/0.99  fof(f2566,plain,(
% 4.58/0.99    k6_relat_1(sK0) = k2_funct_1(sK2) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(duplicate_literal_removal,[],[f2523])).
% 4.58/0.99  fof(f2523,plain,(
% 4.58/0.99    k6_relat_1(sK0) = k2_funct_1(sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 4.58/0.99    inference(superposition,[],[f2362,f1501])).
% 4.58/0.99  fof(f1501,plain,(
% 4.58/0.99    sK0 = k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(resolution,[],[f1408,f1308])).
% 4.58/0.99  fof(f1308,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | sK0 = k1_relat_1(k2_funct_1(sK2))),
% 4.58/0.99    inference(backward_demodulation,[],[f178,f1307])).
% 4.58/0.99  fof(f1307,plain,(
% 4.58/0.99    sK0 = k2_relat_1(sK2)),
% 4.58/0.99    inference(forward_demodulation,[],[f1266,f219])).
% 4.58/0.99  fof(f219,plain,(
% 4.58/0.99    sK0 = k10_relat_1(sK1,k2_relat_1(sK1))),
% 4.58/0.99    inference(backward_demodulation,[],[f143,f218])).
% 4.58/0.99  fof(f218,plain,(
% 4.58/0.99    sK0 = k1_relat_1(sK1)),
% 4.58/0.99    inference(backward_demodulation,[],[f190,f217])).
% 4.58/0.99  fof(f217,plain,(
% 4.58/0.99    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f216,f74])).
% 4.58/0.99  fof(f74,plain,(
% 4.58/0.99    v1_funct_1(sK1)),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f216,plain,(
% 4.58/0.99    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f214,f76])).
% 4.58/0.99  fof(f76,plain,(
% 4.58/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f214,plain,(
% 4.58/0.99    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 4.58/0.99    inference(resolution,[],[f105,f75])).
% 4.58/0.99  fof(f75,plain,(
% 4.58/0.99    v1_funct_2(sK1,sK0,sK0)),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f105,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f50])).
% 4.58/0.99  fof(f50,plain,(
% 4.58/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.58/0.99    inference(flattening,[],[f49])).
% 4.58/0.99  fof(f49,plain,(
% 4.58/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.58/0.99    inference(ennf_transformation,[],[f27])).
% 4.58/0.99  fof(f27,axiom,(
% 4.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 4.58/0.99  fof(f190,plain,(
% 4.58/0.99    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 4.58/0.99    inference(resolution,[],[f108,f76])).
% 4.58/0.99  fof(f108,plain,(
% 4.58/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f55])).
% 4.58/0.99  fof(f55,plain,(
% 4.58/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.58/0.99    inference(ennf_transformation,[],[f18])).
% 4.58/0.99  fof(f18,axiom,(
% 4.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 4.58/0.99  fof(f143,plain,(
% 4.58/0.99    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 4.58/0.99    inference(resolution,[],[f131,f88])).
% 4.58/0.99  fof(f88,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f32])).
% 4.58/0.99  fof(f32,plain,(
% 4.58/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(ennf_transformation,[],[f6])).
% 4.58/0.99  fof(f6,axiom,(
% 4.58/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 4.58/0.99  fof(f131,plain,(
% 4.58/0.99    v1_relat_1(sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f129,f100])).
% 4.58/0.99  fof(f129,plain,(
% 4.58/0.99    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 4.58/0.99    inference(resolution,[],[f92,f76])).
% 4.58/0.99  fof(f1266,plain,(
% 4.58/0.99    k10_relat_1(sK1,k2_relat_1(sK1)) = k2_relat_1(sK2)),
% 4.58/0.99    inference(backward_demodulation,[],[f573,f1253])).
% 4.58/0.99  fof(f573,plain,(
% 4.58/0.99    k2_relat_1(sK2) = k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 4.58/0.99    inference(backward_demodulation,[],[f442,f564])).
% 4.58/0.99  fof(f564,plain,(
% 4.58/0.99    k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1))),
% 4.58/0.99    inference(resolution,[],[f188,f132])).
% 4.58/0.99  fof(f188,plain,(
% 4.58/0.99    ( ! [X5] : (~v1_relat_1(X5) | k2_relat_1(k5_relat_1(X5,sK1)) = k9_relat_1(sK1,k2_relat_1(X5))) )),
% 4.58/0.99    inference(resolution,[],[f91,f131])).
% 4.58/0.99  fof(f91,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f35])).
% 4.58/0.99  fof(f35,plain,(
% 4.58/0.99    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(ennf_transformation,[],[f5])).
% 4.58/0.99  fof(f5,axiom,(
% 4.58/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 4.58/0.99  fof(f442,plain,(
% 4.58/0.99    k2_relat_1(sK2) = k10_relat_1(sK1,k9_relat_1(sK1,k2_relat_1(sK2)))),
% 4.58/0.99    inference(resolution,[],[f312,f223])).
% 4.58/0.99  fof(f223,plain,(
% 4.58/0.99    ( ! [X0] : (~r1_tarski(X0,sK0) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 4.58/0.99    inference(backward_demodulation,[],[f212,f218])).
% 4.58/0.99  fof(f212,plain,(
% 4.58/0.99    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f211,f131])).
% 4.58/0.99  fof(f211,plain,(
% 4.58/0.99    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f209,f81])).
% 4.58/0.99  fof(f81,plain,(
% 4.58/0.99    v2_funct_1(sK1)),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f209,plain,(
% 4.58/0.99    ( ! [X0] : (~v2_funct_1(sK1) | ~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 4.58/0.99    inference(resolution,[],[f106,f74])).
% 4.58/0.99  fof(f106,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f52])).
% 4.58/0.99  fof(f52,plain,(
% 4.58/0.99    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(flattening,[],[f51])).
% 4.58/0.99  fof(f51,plain,(
% 4.58/0.99    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.58/0.99    inference(ennf_transformation,[],[f13])).
% 4.58/0.99  fof(f13,axiom,(
% 4.58/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 4.58/0.99  fof(f178,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 4.58/0.99    inference(subsumption_resolution,[],[f175,f132])).
% 4.58/0.99  fof(f175,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f96,f77])).
% 4.58/0.99  fof(f77,plain,(
% 4.58/0.99    v1_funct_1(sK2)),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f96,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f40])).
% 4.58/0.99  fof(f40,plain,(
% 4.58/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(flattening,[],[f39])).
% 4.58/0.99  fof(f39,plain,(
% 4.58/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.58/0.99    inference(ennf_transformation,[],[f15])).
% 4.58/0.99  fof(f15,axiom,(
% 4.58/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 4.58/0.99  fof(f1408,plain,(
% 4.58/0.99    v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(subsumption_resolution,[],[f1271,f81])).
% 4.58/0.99  fof(f1271,plain,(
% 4.58/0.99    ~v2_funct_1(sK1) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(backward_demodulation,[],[f933,f1253])).
% 4.58/0.99  fof(f933,plain,(
% 4.58/0.99    ~v2_funct_1(k5_relat_1(sK2,sK1)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(backward_demodulation,[],[f427,f931])).
% 4.58/0.99  fof(f931,plain,(
% 4.58/0.99    k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 4.58/0.99    inference(resolution,[],[f647,f76])).
% 4.58/0.99  fof(f647,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK1) = k1_partfun1(sK0,sK0,X0,X1,sK2,sK1)) )),
% 4.58/0.99    inference(resolution,[],[f417,f79])).
% 4.58/0.99  fof(f417,plain,(
% 4.58/0.99    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k5_relat_1(sK2,sK1) = k1_partfun1(X4,X5,X6,X7,sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 4.58/0.99    inference(resolution,[],[f277,f77])).
% 4.58/0.99  fof(f277,plain,(
% 4.58/0.99    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.58/0.99    inference(resolution,[],[f120,f74])).
% 4.58/0.99  fof(f120,plain,(
% 4.58/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f66])).
% 4.58/0.99  fof(f66,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.58/0.99    inference(flattening,[],[f65])).
% 4.58/0.99  fof(f65,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.58/0.99    inference(ennf_transformation,[],[f23])).
% 4.58/0.99  fof(f23,axiom,(
% 4.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 4.58/0.99  fof(f427,plain,(
% 4.58/0.99    ~v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(subsumption_resolution,[],[f426,f77])).
% 4.58/0.99  fof(f426,plain,(
% 4.58/0.99    ~v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) | v2_funct_1(sK2) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 4.58/0.99    inference(subsumption_resolution,[],[f425,f79])).
% 4.58/0.99  fof(f425,plain,(
% 4.58/0.99    ~v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f302,f78])).
% 4.58/0.99  fof(f78,plain,(
% 4.58/0.99    v1_funct_2(sK2,sK0,sK0)),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f302,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_funct_2(X1,X0,sK0) | ~v2_funct_1(k1_partfun1(X0,sK0,sK0,sK0,X1,sK1)) | v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(X1)) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f301,f74])).
% 4.58/0.99  fof(f301,plain,(
% 4.58/0.99    ( ! [X0,X1] : (k1_xboole_0 = sK0 | ~v2_funct_1(k1_partfun1(X0,sK0,sK0,sK0,X1,sK1)) | v2_funct_1(X1) | ~v1_funct_1(sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_2(X1,X0,sK0) | ~v1_funct_1(X1)) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f299,f76])).
% 4.58/0.99  fof(f299,plain,(
% 4.58/0.99    ( ! [X0,X1] : (k1_xboole_0 = sK0 | ~v2_funct_1(k1_partfun1(X0,sK0,sK0,sK0,X1,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v2_funct_1(X1) | ~v1_funct_1(sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_2(X1,X0,sK0) | ~v1_funct_1(X1)) )),
% 4.58/0.99    inference(resolution,[],[f116,f75])).
% 4.58/0.99  fof(f116,plain,(
% 4.58/0.99    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f62])).
% 4.58/0.99  fof(f62,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.58/0.99    inference(flattening,[],[f61])).
% 4.58/0.99  fof(f61,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.58/0.99    inference(ennf_transformation,[],[f25])).
% 4.58/0.99  fof(f25,axiom,(
% 4.58/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 4.58/0.99  fof(f2362,plain,(
% 4.58/0.99    k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(subsumption_resolution,[],[f2361,f1501])).
% 4.58/0.99  fof(f2361,plain,(
% 4.58/0.99    sK0 != k1_relat_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(forward_demodulation,[],[f2360,f220])).
% 4.58/0.99  fof(f220,plain,(
% 4.58/0.99    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 4.58/0.99    inference(backward_demodulation,[],[f182,f218])).
% 4.58/0.99  fof(f182,plain,(
% 4.58/0.99    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 4.58/0.99    inference(subsumption_resolution,[],[f181,f131])).
% 4.58/0.99  fof(f181,plain,(
% 4.58/0.99    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f179,f81])).
% 4.58/0.99  fof(f179,plain,(
% 4.58/0.99    ~v2_funct_1(sK1) | k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 4.58/0.99    inference(resolution,[],[f97,f74])).
% 4.58/0.99  fof(f97,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f40])).
% 4.58/0.99  fof(f2360,plain,(
% 4.58/0.99    k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1)) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(subsumption_resolution,[],[f2359,f1509])).
% 4.58/0.99  fof(f1509,plain,(
% 4.58/0.99    k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(resolution,[],[f1262,f1408])).
% 4.58/0.99  fof(f1262,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | k2_funct_1(sK1) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))),
% 4.58/0.99    inference(backward_demodulation,[],[f365,f1253])).
% 4.58/0.99  fof(f365,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2))),
% 4.58/0.99    inference(subsumption_resolution,[],[f360,f132])).
% 4.58/0.99  fof(f360,plain,(
% 4.58/0.99    k2_funct_1(k5_relat_1(sK2,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f236,f77])).
% 4.58/0.99  fof(f236,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_funct_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f235,f131])).
% 4.58/0.99  fof(f235,plain,(
% 4.58/0.99    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f233,f81])).
% 4.58/0.99  fof(f233,plain,(
% 4.58/0.99    ( ! [X0] : (~v2_funct_1(sK1) | ~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(resolution,[],[f98,f74])).
% 4.58/0.99  fof(f98,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f42])).
% 4.58/0.99  fof(f42,plain,(
% 4.58/0.99    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(flattening,[],[f41])).
% 4.58/0.99  fof(f41,plain,(
% 4.58/0.99    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.58/0.99    inference(ennf_transformation,[],[f16])).
% 4.58/0.99  fof(f16,axiom,(
% 4.58/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 4.58/0.99  fof(f2359,plain,(
% 4.58/0.99    k2_funct_1(sK1) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1)) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(subsumption_resolution,[],[f2340,f147])).
% 4.58/0.99  fof(f147,plain,(
% 4.58/0.99    v1_relat_1(k2_funct_1(sK1))),
% 4.58/0.99    inference(subsumption_resolution,[],[f146,f131])).
% 4.58/0.99  fof(f146,plain,(
% 4.58/0.99    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f144,f81])).
% 4.58/0.99  fof(f144,plain,(
% 4.58/0.99    ~v2_funct_1(sK1) | v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 4.58/0.99    inference(resolution,[],[f93,f74])).
% 4.58/0.99  fof(f93,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f38])).
% 4.58/0.99  fof(f38,plain,(
% 4.58/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(flattening,[],[f37])).
% 4.58/0.99  fof(f37,plain,(
% 4.58/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.58/0.99    inference(ennf_transformation,[],[f12])).
% 4.58/0.99  fof(f12,axiom,(
% 4.58/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 4.58/0.99  fof(f2340,plain,(
% 4.58/0.99    k2_funct_1(sK1) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1)) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k1_xboole_0 = sK0 | ~v1_relat_1(k2_funct_1(sK1))),
% 4.58/0.99    inference(resolution,[],[f1584,f152])).
% 4.58/0.99  fof(f152,plain,(
% 4.58/0.99    v1_funct_1(k2_funct_1(sK1))),
% 4.58/0.99    inference(subsumption_resolution,[],[f151,f131])).
% 4.58/0.99  fof(f151,plain,(
% 4.58/0.99    v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f149,f81])).
% 4.58/0.99  fof(f149,plain,(
% 4.58/0.99    ~v2_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 4.58/0.99    inference(resolution,[],[f94,f74])).
% 4.58/0.99  fof(f94,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f38])).
% 4.58/0.99  fof(f1584,plain,(
% 4.58/0.99    ( ! [X1] : (~v1_funct_1(X1) | k5_relat_1(X1,k2_funct_1(sK2)) != X1 | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k1_xboole_0 = sK0 | ~v1_relat_1(X1)) )),
% 4.58/0.99    inference(subsumption_resolution,[],[f1547,f1491])).
% 4.58/0.99  fof(f1491,plain,(
% 4.58/0.99    v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(resolution,[],[f1408,f148])).
% 4.58/0.99  fof(f148,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 4.58/0.99    inference(subsumption_resolution,[],[f145,f132])).
% 4.58/0.99  fof(f145,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f93,f77])).
% 4.58/0.99  fof(f1547,plain,(
% 4.58/0.99    ( ! [X1] : (k1_xboole_0 = sK0 | k5_relat_1(X1,k2_funct_1(sK2)) != X1 | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.58/0.99    inference(resolution,[],[f1492,f99])).
% 4.58/0.99  fof(f99,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_funct_1(X1) | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f44])).
% 4.58/0.99  fof(f44,plain,(
% 4.58/0.99    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(flattening,[],[f43])).
% 4.58/0.99  fof(f43,plain,(
% 4.58/0.99    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.58/0.99    inference(ennf_transformation,[],[f14])).
% 4.58/0.99  fof(f14,axiom,(
% 4.58/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 4.58/0.99  fof(f1492,plain,(
% 4.58/0.99    v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(resolution,[],[f1408,f153])).
% 4.58/0.99  fof(f153,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 4.58/0.99    inference(subsumption_resolution,[],[f150,f132])).
% 4.58/0.99  fof(f150,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f94,f77])).
% 4.58/0.99  fof(f1504,plain,(
% 4.58/0.99    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | k1_xboole_0 = sK0),
% 4.58/0.99    inference(duplicate_literal_removal,[],[f1503])).
% 4.58/0.99  fof(f1503,plain,(
% 4.58/0.99    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 4.58/0.99    inference(resolution,[],[f1408,f1354])).
% 4.58/0.99  fof(f1354,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | k1_xboole_0 = sK0 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 4.58/0.99    inference(trivial_inequality_removal,[],[f1317])).
% 4.58/0.99  fof(f1317,plain,(
% 4.58/0.99    sK0 != sK0 | ~v2_funct_1(sK2) | k1_xboole_0 = sK0 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 4.58/0.99    inference(backward_demodulation,[],[f551,f1307])).
% 4.58/0.99  fof(f551,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | sK0 != k2_relat_1(sK2) | k1_xboole_0 = sK0 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 4.58/0.99    inference(backward_demodulation,[],[f298,f548])).
% 4.58/0.99  fof(f548,plain,(
% 4.58/0.99    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 4.58/0.99    inference(superposition,[],[f168,f308])).
% 4.58/0.99  fof(f308,plain,(
% 4.58/0.99    sK2 = k7_relat_1(sK2,sK0)),
% 4.58/0.99    inference(subsumption_resolution,[],[f307,f132])).
% 4.58/0.99  fof(f307,plain,(
% 4.58/0.99    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f162,f107])).
% 4.58/0.99  fof(f107,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f54])).
% 4.58/0.99  fof(f54,plain,(
% 4.58/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(flattening,[],[f53])).
% 4.58/0.99  fof(f53,plain,(
% 4.58/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.58/0.99    inference(ennf_transformation,[],[f7])).
% 4.58/0.99  fof(f7,axiom,(
% 4.58/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 4.58/0.99  fof(f162,plain,(
% 4.58/0.99    v4_relat_1(sK2,sK0)),
% 4.58/0.99    inference(resolution,[],[f109,f79])).
% 4.58/0.99  fof(f109,plain,(
% 4.58/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f56])).
% 4.58/0.99  fof(f168,plain,(
% 4.58/0.99    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 4.58/0.99    inference(resolution,[],[f132,f101])).
% 4.58/0.99  fof(f101,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f45])).
% 4.58/0.99  fof(f45,plain,(
% 4.58/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.58/0.99    inference(ennf_transformation,[],[f4])).
% 4.58/0.99  fof(f4,axiom,(
% 4.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 4.58/0.99  fof(f298,plain,(
% 4.58/0.99    ~v2_funct_1(sK2) | k1_xboole_0 = sK0 | sK0 != k9_relat_1(sK2,sK0) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 4.58/0.99    inference(forward_demodulation,[],[f297,f204])).
% 4.58/0.99  fof(f204,plain,(
% 4.58/0.99    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0)),
% 4.58/0.99    inference(forward_demodulation,[],[f202,f193])).
% 4.58/0.99  fof(f193,plain,(
% 4.58/0.99    ( ! [X1] : (k9_relat_1(sK2,X1) = k7_relset_1(sK0,sK0,sK2,X1)) )),
% 4.58/0.99    inference(resolution,[],[f115,f79])).
% 4.58/0.99  fof(f115,plain,(
% 4.58/0.99    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f60])).
% 4.58/0.99  fof(f60,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.58/0.99    inference(ennf_transformation,[],[f19])).
% 4.58/0.99  fof(f19,axiom,(
% 4.58/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 4.58/0.99  fof(f202,plain,(
% 4.58/0.99    k7_relset_1(sK0,sK0,sK2,sK0) = k2_relset_1(sK0,sK0,sK2)),
% 4.58/0.99    inference(resolution,[],[f111,f79])).
% 4.58/0.99  fof(f111,plain,(
% 4.58/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f57])).
% 4.58/0.99  fof(f57,plain,(
% 4.58/0.99    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.58/0.99    inference(ennf_transformation,[],[f21])).
% 4.58/0.99  fof(f21,axiom,(
% 4.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 4.58/0.99  fof(f297,plain,(
% 4.58/0.99    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 4.58/0.99    inference(subsumption_resolution,[],[f296,f77])).
% 4.58/0.99  fof(f296,plain,(
% 4.58/0.99    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 4.58/0.99    inference(subsumption_resolution,[],[f292,f79])).
% 4.58/0.99  fof(f292,plain,(
% 4.58/0.99    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | sK0 != k2_relset_1(sK0,sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 4.58/0.99    inference(resolution,[],[f128,f78])).
% 4.58/0.99  fof(f128,plain,(
% 4.58/0.99    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_1(X2)) )),
% 4.58/0.99    inference(forward_demodulation,[],[f113,f83])).
% 4.58/0.99  fof(f83,plain,(
% 4.58/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f24])).
% 4.58/0.99  fof(f24,axiom,(
% 4.58/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 4.58/0.99  fof(f113,plain,(
% 4.58/0.99    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f59])).
% 4.58/0.99  fof(f59,plain,(
% 4.58/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.58/0.99    inference(flattening,[],[f58])).
% 4.58/0.99  fof(f58,plain,(
% 4.58/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.58/0.99    inference(ennf_transformation,[],[f26])).
% 4.58/0.99  fof(f26,axiom,(
% 4.58/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 4.58/0.99  fof(f126,plain,(
% 4.58/0.99    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 4.58/0.99    inference(forward_demodulation,[],[f82,f83])).
% 4.58/0.99  fof(f82,plain,(
% 4.58/0.99    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f485,plain,(
% 4.58/0.99    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 4.58/0.99    inference(superposition,[],[f142,f218])).
% 4.58/0.99  fof(f142,plain,(
% 4.58/0.99    k1_xboole_0 != k1_relat_1(sK1) | k1_xboole_0 = sK1),
% 4.58/0.99    inference(resolution,[],[f131,f89])).
% 4.58/0.99  fof(f89,plain,(
% 4.58/0.99    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 4.58/0.99    inference(cnf_transformation,[],[f34])).
% 4.58/0.99  fof(f34,plain,(
% 4.58/0.99    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(flattening,[],[f33])).
% 4.58/0.99  fof(f33,plain,(
% 4.58/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 4.58/0.99    inference(ennf_transformation,[],[f8])).
% 4.58/0.99  fof(f8,axiom,(
% 4.58/0.99    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 4.58/0.99  fof(f1253,plain,(
% 4.58/0.99    sK1 = k5_relat_1(sK2,sK1)),
% 4.58/0.99    inference(resolution,[],[f974,f936])).
% 4.58/0.99  fof(f936,plain,(
% 4.58/0.99    ~m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k5_relat_1(sK2,sK1)),
% 4.58/0.99    inference(forward_demodulation,[],[f934,f931])).
% 4.58/0.99  fof(f934,plain,(
% 4.58/0.99    ~m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 4.58/0.99    inference(backward_demodulation,[],[f232,f931])).
% 4.58/0.99  fof(f232,plain,(
% 4.58/0.99    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 4.58/0.99    inference(subsumption_resolution,[],[f231,f76])).
% 4.58/0.99  fof(f231,plain,(
% 4.58/0.99    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.58/0.99    inference(resolution,[],[f118,f80])).
% 4.58/0.99  fof(f80,plain,(
% 4.58/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 4.58/0.99    inference(cnf_transformation,[],[f71])).
% 4.58/0.99  fof(f118,plain,(
% 4.58/0.99    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.58/0.99    inference(cnf_transformation,[],[f73])).
% 4.58/0.99  fof(f974,plain,(
% 4.58/0.99    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.58/0.99    inference(forward_demodulation,[],[f973,f931])).
% 4.58/0.99  fof(f973,plain,(
% 4.58/0.99    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.58/0.99    inference(resolution,[],[f656,f76])).
% 4.58/0.99  fof(f656,plain,(
% 4.58/0.99    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK0,X0,X1,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 4.58/0.99    inference(resolution,[],[f433,f79])).
% 4.58/0.99  fof(f433,plain,(
% 4.58/0.99    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | m1_subset_1(k1_partfun1(X4,X5,X6,X7,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X7))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 4.58/0.99    inference(resolution,[],[f280,f77])).
% 4.58/0.99  fof(f280,plain,(
% 4.58/0.99    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | m1_subset_1(k1_partfun1(X2,X3,X0,X1,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.58/0.99    inference(resolution,[],[f122,f74])).
% 4.58/0.99  fof(f122,plain,(
% 4.58/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.58/0.99    inference(cnf_transformation,[],[f68])).
% 4.58/0.99  fof(f68,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.58/0.99    inference(flattening,[],[f67])).
% 4.58/0.99  fof(f67,plain,(
% 4.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.58/0.99    inference(ennf_transformation,[],[f22])).
% 4.58/0.99  fof(f22,axiom,(
% 4.58/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 4.58/0.99  fof(f3361,plain,(
% 4.58/0.99    sK2 = k5_relat_1(sK2,k1_xboole_0)),
% 4.58/0.99    inference(forward_demodulation,[],[f3065,f671])).
% 4.58/0.99  fof(f671,plain,(
% 4.58/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.58/0.99    inference(equality_resolution,[],[f446])).
% 4.58/0.99  fof(f446,plain,(
% 4.58/0.99    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) )),
% 4.58/0.99    inference(superposition,[],[f137,f86])).
% 4.58/0.99  fof(f86,plain,(
% 4.58/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.58/0.99    inference(cnf_transformation,[],[f9])).
% 4.58/0.99  fof(f9,axiom,(
% 4.58/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 4.58/0.99  fof(f137,plain,(
% 4.58/0.99    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0)) )),
% 4.58/0.99    inference(resolution,[],[f89,f84])).
% 4.58/0.99  fof(f84,plain,(
% 4.58/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.58/0.99    inference(cnf_transformation,[],[f11])).
% 4.58/0.99  fof(f11,axiom,(
% 4.58/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 4.58/0.99  fof(f3065,plain,(
% 4.58/0.99    sK2 = k5_relat_1(sK2,k6_relat_1(k1_xboole_0))),
% 4.58/0.99    inference(backward_demodulation,[],[f443,f3020])).
% 4.58/0.99  fof(f3031,plain,(
% 4.58/0.99    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 4.58/0.99    inference(backward_demodulation,[],[f173,f3020])).
% 4.58/0.99  fof(f5550,plain,(
% 4.58/0.99    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 4.58/0.99    inference(backward_demodulation,[],[f3335,f5488])).
% 4.58/0.99  fof(f3335,plain,(
% 4.58/0.99    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 4.58/0.99    inference(forward_demodulation,[],[f3025,f671])).
% 4.58/0.99  fof(f3025,plain,(
% 4.58/0.99    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k6_relat_1(k1_xboole_0))),
% 4.58/0.99    inference(backward_demodulation,[],[f126,f3020])).
% 4.58/0.99  % SZS output end Proof for theBenchmark
% 4.58/0.99  % (13841)------------------------------
% 4.58/0.99  % (13841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/0.99  % (13841)Termination reason: Refutation
% 4.58/0.99  
% 4.58/0.99  % (13841)Memory used [KB]: 5117
% 4.58/0.99  % (13841)Time elapsed: 0.443 s
% 4.58/0.99  % (13841)------------------------------
% 4.58/0.99  % (13841)------------------------------
% 4.58/0.99  % (13833)Success in time 0.631 s
%------------------------------------------------------------------------------
