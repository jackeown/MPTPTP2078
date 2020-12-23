%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  139 (118113 expanded)
%              Number of leaves         :   13 (24620 expanded)
%              Depth                    :   41
%              Number of atoms          :  338 (531048 expanded)
%              Number of equality atoms :  138 (117762 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(resolution,[],[f628,f493])).

fof(f493,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f467,f485])).

fof(f485,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f484,f469])).

fof(f469,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f440,f448])).

fof(f448,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f447,f67])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f447,plain,(
    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f446,f358])).

fof(f358,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f354,f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f354,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f351,f254])).

fof(f254,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f253,f229])).

fof(f229,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f148,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f151,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f151,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f150,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f150,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f145,f66])).

fof(f145,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f120,f131])).

fof(f131,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f111,f123])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f77,f79])).

fof(f79,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f36,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f35,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f75,f103,f110])).

fof(f110,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(forward_demodulation,[],[f106,f105])).

fof(f105,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f103,f63])).

fof(f106,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f103,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f94,f84])).

fof(f84,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f37,f81])).

fof(f81,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f90,f85])).

fof(f85,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f82,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f89,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f89,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f88,f85])).

fof(f88,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f78,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f36,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f75,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f32,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK2) ),
    inference(resolution,[],[f109,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f103,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f141,f66])).

fof(f141,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f103,f131])).

fof(f253,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f146,f152])).

fof(f146,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f136,f66])).

fof(f136,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f131])).

fof(f351,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f343,f33])).

fof(f343,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(resolution,[],[f323,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f323,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f221,f152])).

fof(f221,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f211,f44])).

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f94,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f139,f44])).

fof(f139,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f87,f131])).

fof(f87,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f84,f43])).

fof(f446,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f445,f44])).

fof(f445,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f371,f67])).

fof(f371,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f96,f358])).

fof(f96,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f83,f43])).

fof(f83,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f46])).

fof(f440,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f439,f358])).

fof(f439,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f369,f44])).

fof(f369,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f93,f358])).

fof(f93,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f89,f43])).

fof(f484,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f378,f448])).

fof(f378,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f111,f358])).

fof(f467,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f437,f448])).

fof(f437,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f436,f434])).

fof(f434,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f360,f67])).

fof(f360,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f36,f358])).

fof(f436,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f435,f67])).

fof(f435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f361,f358])).

fof(f361,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f75,f358])).

fof(f628,plain,(
    ! [X8] : v1_funct_2(k1_xboole_0,k1_xboole_0,X8) ),
    inference(subsumption_resolution,[],[f620,f625])).

fof(f625,plain,(
    ! [X2,X3] : k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f617,f469])).

fof(f617,plain,(
    ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f609,f63])).

fof(f609,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(subsumption_resolution,[],[f608,f44])).

fof(f608,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f607,f501])).

fof(f501,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f500,f485])).

fof(f500,plain,(
    sK2 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f494,f44])).

fof(f494,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | sK2 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f471,f485])).

fof(f471,plain,
    ( sK2 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK2,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f453,f448])).

fof(f453,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(k1_xboole_0))
    | sK2 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f87,f448])).

fof(f607,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f606,f451])).

fof(f451,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f85,f448])).

fof(f606,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f604,f44])).

fof(f604,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f64,f469])).

fof(f620,plain,(
    ! [X8] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X8,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X8) ) ),
    inference(resolution,[],[f609,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15481)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (15482)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (15497)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (15496)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (15479)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (15481)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (15482)Refutation not found, incomplete strategy% (15482)------------------------------
% 0.22/0.52  % (15482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15480)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.25/0.52  % (15487)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.25/0.52  % (15490)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.25/0.52  % (15482)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (15482)Memory used [KB]: 10618
% 1.25/0.52  % (15482)Time elapsed: 0.100 s
% 1.25/0.52  % (15482)------------------------------
% 1.25/0.52  % (15482)------------------------------
% 1.25/0.53  % (15492)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.25/0.53  % (15485)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.25/0.53  % (15488)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.25/0.53  % (15499)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.25/0.53  % (15491)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.25/0.54  % (15486)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.25/0.54  % (15493)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.25/0.54  % (15483)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.25/0.54  % (15477)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.54  % (15495)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.25/0.54  % (15476)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f629,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(resolution,[],[f628,f493])).
% 1.39/0.54  fof(f493,plain,(
% 1.39/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.39/0.54    inference(backward_demodulation,[],[f467,f485])).
% 1.39/0.54  fof(f485,plain,(
% 1.39/0.54    k1_xboole_0 = sK2),
% 1.39/0.54    inference(subsumption_resolution,[],[f484,f469])).
% 1.39/0.54  fof(f469,plain,(
% 1.39/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(backward_demodulation,[],[f440,f448])).
% 1.39/0.54  fof(f448,plain,(
% 1.39/0.54    k1_xboole_0 = sK3),
% 1.39/0.54    inference(forward_demodulation,[],[f447,f67])).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.54  fof(f447,plain,(
% 1.39/0.54    sK3 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.39/0.54    inference(forward_demodulation,[],[f446,f358])).
% 1.39/0.54  fof(f358,plain,(
% 1.39/0.54    k1_xboole_0 = sK0),
% 1.39/0.54    inference(subsumption_resolution,[],[f354,f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.39/0.54    inference(flattening,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.39/0.54    inference(ennf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.39/0.54    inference(negated_conjecture,[],[f17])).
% 1.39/0.54  fof(f17,conjecture,(
% 1.39/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.39/0.54  fof(f354,plain,(
% 1.39/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.39/0.54    inference(resolution,[],[f351,f254])).
% 1.39/0.54  fof(f254,plain,(
% 1.39/0.54    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(subsumption_resolution,[],[f253,f229])).
% 1.39/0.54  fof(f229,plain,(
% 1.39/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f228])).
% 1.39/0.54  fof(f228,plain,(
% 1.39/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f148,f152])).
% 1.39/0.54  fof(f152,plain,(
% 1.39/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK1),
% 1.39/0.54    inference(forward_demodulation,[],[f151,f66])).
% 1.39/0.54  fof(f66,plain,(
% 1.39/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(equality_resolution,[],[f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f151,plain,(
% 1.39/0.54    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(subsumption_resolution,[],[f150,f44])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.54  fof(f150,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(forward_demodulation,[],[f145,f66])).
% 1.39/0.54  fof(f145,plain,(
% 1.39/0.54    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f120,f131])).
% 1.39/0.54  fof(f131,plain,(
% 1.39/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f125])).
% 1.39/0.54  fof(f125,plain,(
% 1.39/0.54    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f111,f123])).
% 1.39/0.54  fof(f123,plain,(
% 1.39/0.54    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f77,f79])).
% 1.39/0.54  fof(f79,plain,(
% 1.39/0.54    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f36,f63])).
% 1.39/0.54  fof(f63,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f28])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f12])).
% 1.39/0.54  fof(f12,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(subsumption_resolution,[],[f76,f36])).
% 1.39/0.54  fof(f76,plain,(
% 1.39/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.54    inference(resolution,[],[f35,f57])).
% 1.39/0.54  fof(f57,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(flattening,[],[f26])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    v1_funct_2(sK3,sK0,sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.39/0.54    inference(global_subsumption,[],[f75,f103,f110])).
% 1.39/0.54  fof(f110,plain,(
% 1.39/0.54    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 1.39/0.54    inference(forward_demodulation,[],[f106,f105])).
% 1.39/0.54  fof(f105,plain,(
% 1.39/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 1.39/0.54    inference(resolution,[],[f103,f63])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2)),
% 1.39/0.54    inference(resolution,[],[f103,f56])).
% 1.39/0.54  fof(f56,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f103,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.39/0.54    inference(resolution,[],[f94,f84])).
% 1.39/0.54  fof(f84,plain,(
% 1.39/0.54    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.39/0.54    inference(backward_demodulation,[],[f37,f81])).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f36,f49])).
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f94,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f90,f85])).
% 1.39/0.54  fof(f85,plain,(
% 1.39/0.54    v1_relat_1(sK3)),
% 1.39/0.54    inference(subsumption_resolution,[],[f82,f51])).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.54  fof(f82,plain,(
% 1.39/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f36,f50])).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.39/0.54  fof(f90,plain,(
% 1.39/0.54    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.39/0.54    inference(resolution,[],[f89,f64])).
% 1.39/0.54  fof(f64,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f30])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.39/0.54    inference(flattening,[],[f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.39/0.54    inference(ennf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.39/0.54  fof(f89,plain,(
% 1.39/0.54    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f88,f85])).
% 1.39/0.54  fof(f88,plain,(
% 1.39/0.54    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f78,f48])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f23])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.39/0.54  fof(f78,plain,(
% 1.39/0.54    v4_relat_1(sK3,sK0)),
% 1.39/0.54    inference(resolution,[],[f36,f65])).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.39/0.54    inference(pure_predicate_removal,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.39/0.54    inference(subsumption_resolution,[],[f32,f34])).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    v1_funct_1(sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f120,plain,(
% 1.39/0.54    ~r1_tarski(k2_zfmisc_1(sK0,sK2),sK3) | sK3 = k2_zfmisc_1(sK0,sK2)),
% 1.39/0.54    inference(resolution,[],[f109,f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.54  fof(f109,plain,(
% 1.39/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.39/0.54    inference(resolution,[],[f103,f46])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.54  fof(f148,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(forward_demodulation,[],[f141,f66])).
% 1.39/0.54  fof(f141,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f103,f131])).
% 1.39/0.54  fof(f253,plain,(
% 1.39/0.54    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f252])).
% 1.39/0.54  fof(f252,plain,(
% 1.39/0.54    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f146,f152])).
% 1.39/0.54  fof(f146,plain,(
% 1.39/0.54    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(forward_demodulation,[],[f136,f66])).
% 1.39/0.54  fof(f136,plain,(
% 1.39/0.54    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f75,f131])).
% 1.39/0.54  fof(f351,plain,(
% 1.39/0.54    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.39/0.54    inference(subsumption_resolution,[],[f343,f33])).
% 1.39/0.54  fof(f343,plain,(
% 1.39/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 1.39/0.54    inference(resolution,[],[f323,f74])).
% 1.39/0.54  fof(f74,plain,(
% 1.39/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.39/0.54    inference(equality_resolution,[],[f73])).
% 1.39/0.54  fof(f73,plain,(
% 1.39/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.39/0.54    inference(equality_resolution,[],[f52])).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f323,plain,(
% 1.39/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f321])).
% 1.39/0.54  fof(f321,plain,(
% 1.39/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1) )),
% 1.39/0.54    inference(superposition,[],[f221,f152])).
% 1.39/0.54  fof(f221,plain,(
% 1.39/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f211,f44])).
% 1.39/0.54  fof(f211,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 1.39/0.54    inference(superposition,[],[f94,f147])).
% 1.39/0.54  fof(f147,plain,(
% 1.39/0.54    k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(subsumption_resolution,[],[f139,f44])).
% 1.39/0.54  fof(f139,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.39/0.54    inference(superposition,[],[f87,f131])).
% 1.39/0.54  fof(f87,plain,(
% 1.39/0.54    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f84,f43])).
% 1.39/0.54  fof(f446,plain,(
% 1.39/0.54    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.54    inference(subsumption_resolution,[],[f445,f44])).
% 1.39/0.54  fof(f445,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.54    inference(forward_demodulation,[],[f371,f67])).
% 1.39/0.54  fof(f371,plain,(
% 1.39/0.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.54    inference(backward_demodulation,[],[f96,f358])).
% 1.39/0.54  fof(f96,plain,(
% 1.39/0.54    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.54    inference(resolution,[],[f83,f43])).
% 1.39/0.54  fof(f83,plain,(
% 1.39/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.54    inference(resolution,[],[f36,f46])).
% 1.39/0.54  fof(f440,plain,(
% 1.39/0.54    k1_xboole_0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(forward_demodulation,[],[f439,f358])).
% 1.39/0.54  fof(f439,plain,(
% 1.39/0.54    sK0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(subsumption_resolution,[],[f369,f44])).
% 1.39/0.54  fof(f369,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(backward_demodulation,[],[f93,f358])).
% 1.39/0.54  fof(f93,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f89,f43])).
% 1.39/0.54  fof(f484,plain,(
% 1.39/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2),
% 1.39/0.54    inference(forward_demodulation,[],[f378,f448])).
% 1.39/0.54  fof(f378,plain,(
% 1.39/0.54    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.39/0.54    inference(backward_demodulation,[],[f111,f358])).
% 1.39/0.54  fof(f467,plain,(
% 1.39/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 1.39/0.54    inference(backward_demodulation,[],[f437,f448])).
% 1.39/0.54  fof(f437,plain,(
% 1.39/0.54    ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.39/0.54    inference(subsumption_resolution,[],[f436,f434])).
% 1.39/0.54  fof(f434,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.54    inference(forward_demodulation,[],[f360,f67])).
% 1.39/0.54  fof(f360,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.39/0.54    inference(backward_demodulation,[],[f36,f358])).
% 1.39/0.54  fof(f436,plain,(
% 1.39/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.39/0.54    inference(forward_demodulation,[],[f435,f67])).
% 1.39/0.54  fof(f435,plain,(
% 1.39/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.39/0.54    inference(forward_demodulation,[],[f361,f358])).
% 1.39/0.54  fof(f361,plain,(
% 1.39/0.54    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.39/0.54    inference(backward_demodulation,[],[f75,f358])).
% 1.39/0.54  fof(f628,plain,(
% 1.39/0.54    ( ! [X8] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X8)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f620,f625])).
% 1.39/0.54  fof(f625,plain,(
% 1.39/0.54    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 1.39/0.54    inference(forward_demodulation,[],[f617,f469])).
% 1.39/0.54  fof(f617,plain,(
% 1.39/0.54    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 1.39/0.54    inference(resolution,[],[f609,f63])).
% 1.39/0.54  fof(f609,plain,(
% 1.39/0.54    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f608,f44])).
% 1.39/0.54  fof(f608,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(forward_demodulation,[],[f607,f501])).
% 1.39/0.54  fof(f501,plain,(
% 1.39/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(forward_demodulation,[],[f500,f485])).
% 1.39/0.54  fof(f500,plain,(
% 1.39/0.54    sK2 = k2_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f494,f44])).
% 1.39/0.54  fof(f494,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | sK2 = k2_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(backward_demodulation,[],[f471,f485])).
% 1.39/0.54  fof(f471,plain,(
% 1.39/0.54    sK2 = k2_relat_1(k1_xboole_0) | ~r1_tarski(sK2,k2_relat_1(k1_xboole_0))),
% 1.39/0.54    inference(forward_demodulation,[],[f453,f448])).
% 1.39/0.54  fof(f453,plain,(
% 1.39/0.54    ~r1_tarski(sK2,k2_relat_1(k1_xboole_0)) | sK2 = k2_relat_1(sK3)),
% 1.39/0.54    inference(backward_demodulation,[],[f87,f448])).
% 1.39/0.54  fof(f607,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f606,f451])).
% 1.39/0.54  fof(f451,plain,(
% 1.39/0.54    v1_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(backward_demodulation,[],[f85,f448])).
% 1.39/0.54  fof(f606,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f604,f44])).
% 1.39/0.54  fof(f604,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(superposition,[],[f64,f469])).
% 1.39/0.54  fof(f620,plain,(
% 1.39/0.54    ( ! [X8] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X8,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X8)) )),
% 1.39/0.54    inference(resolution,[],[f609,f71])).
% 1.39/0.54  fof(f71,plain,(
% 1.39/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f54])).
% 1.39/0.54  fof(f54,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (15481)------------------------------
% 1.39/0.54  % (15481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (15481)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (15481)Memory used [KB]: 6396
% 1.39/0.54  % (15481)Time elapsed: 0.100 s
% 1.39/0.54  % (15481)------------------------------
% 1.39/0.54  % (15481)------------------------------
% 1.39/0.55  % (15475)Success in time 0.179 s
%------------------------------------------------------------------------------
