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
% DateTime   : Thu Dec  3 13:01:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  138 (1218 expanded)
%              Number of leaves         :   16 ( 227 expanded)
%              Depth                    :   23
%              Number of atoms          :  410 (7345 expanded)
%              Number of equality atoms :  109 (1990 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1004,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1003,f104])).

fof(f104,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1003,plain,(
    ~ v5_relat_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f1002,f911])).

fof(f911,plain,(
    sK1 = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f387,f894])).

fof(f894,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f893,f87])).

fof(f87,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f65,f50])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f893,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f888,f103])).

fof(f103,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f888,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f116,f860])).

fof(f860,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f855,f818])).

fof(f818,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f44,f817])).

fof(f817,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f815,f50])).

fof(f815,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k5_relat_1(sK3,sK4) = k1_partfun1(X15,X16,sK1,sK2,sK3,sK4) ) ),
    inference(resolution,[],[f666,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f666,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(X0,sK4) = k1_partfun1(X1,X2,sK1,sK2,X0,sK4) ) ),
    inference(resolution,[],[f429,f43])).

fof(f429,plain,(
    ! [X26,X24,X23,X25,X22] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ v1_funct_1(X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_partfun1(X23,X24,X25,X26,X22,sK4) = k5_relat_1(X22,sK4) ) ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f44,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f855,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f829,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f829,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f828,f48])).

fof(f828,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f827,f43])).

fof(f827,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f826,f41])).

fof(f826,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f820,f50])).

fof(f820,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f78,f817])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK4,k2_relat_1(k5_relat_1(X0,sK4)))
      | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f113,f86])).

fof(f86,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f65,f43])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ v1_relat_1(X0)
      | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4))
      | ~ v5_relat_1(sK4,k2_relat_1(k5_relat_1(X0,sK4))) ) ),
    inference(resolution,[],[f51,f99])).

fof(f99,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_relat_1(sK4))
      | k2_relat_1(sK4) = X1
      | ~ v5_relat_1(sK4,X1) ) ),
    inference(resolution,[],[f64,f93])).

fof(f93,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK4),X0)
      | ~ v5_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f59,f86])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f64,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f387,plain,(
    sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f384,f358])).

fof(f358,plain,(
    sK1 = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(backward_demodulation,[],[f157,f356])).

fof(f356,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f143,f355])).

fof(f355,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f354,f42])).

fof(f42,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f354,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ v1_funct_2(sK4,sK1,sK2) ),
    inference(subsumption_resolution,[],[f352,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f352,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ v1_funct_2(sK4,sK1,sK2) ),
    inference(resolution,[],[f75,f43])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f143,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f157,plain,(
    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f156,f86])).

fof(f156,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f154,f41])).

fof(f154,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f384,plain,(
    k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) ),
    inference(resolution,[],[f381,f86])).

fof(f381,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f380,f86])).

fof(f380,plain,(
    ! [X0] :
      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f378,f41])).

fof(f378,plain,(
    ! [X0] :
      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f136,f45])).

fof(f136,plain,(
    ! [X2,X3] :
      ( ~ v2_funct_1(X3)
      | k2_relat_1(k5_relat_1(X2,k2_funct_1(X3))) = k9_relat_1(k2_funct_1(X3),k2_relat_1(X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1002,plain,(
    ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),sK2)) ),
    inference(subsumption_resolution,[],[f998,f147])).

fof(f147,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f47,f146])).

fof(f146,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f67,f50])).

fof(f47,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f998,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),sK2)) ),
    inference(backward_demodulation,[],[f873,f911])).

fof(f873,plain,
    ( ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),sK2))
    | k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(forward_demodulation,[],[f870,f866])).

fof(f866,plain,(
    k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f839,f860])).

fof(f839,plain,(
    k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))) ),
    inference(resolution,[],[f825,f381])).

fof(f825,plain,(
    v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f824,f50])).

fof(f824,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f823,f48])).

fof(f823,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f822,f43])).

fof(f822,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f819,f41])).

fof(f819,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f526,f817])).

fof(f526,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_relat_1(k1_partfun1(X1,X2,X4,X5,X0,X3))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f78,f65])).

fof(f870,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ v5_relat_1(sK3,k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4)))) ),
    inference(backward_demodulation,[],[f847,f866])).

fof(f847,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))))
    | k2_relat_1(sK3) = k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))) ),
    inference(forward_demodulation,[],[f845,f839])).

fof(f845,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4)))
    | ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4)))) ),
    inference(backward_demodulation,[],[f215,f839])).

fof(f215,plain,
    ( ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))))
    | k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) ),
    inference(forward_demodulation,[],[f214,f138])).

fof(f138,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) ),
    inference(resolution,[],[f134,f87])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f52,f86])).

fof(f214,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4)))
    | ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f208,f138])).

fof(f208,plain,
    ( k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3)))
    | ~ v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3)))) ),
    inference(resolution,[],[f203,f100])).

fof(f100,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK3))
      | k2_relat_1(sK3) = X2
      | ~ v5_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f64,f94])).

fof(f94,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(sK3),X1)
      | ~ v5_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f59,f87])).

fof(f203,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) ),
    inference(forward_demodulation,[],[f202,f167])).

fof(f167,plain,(
    ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ),
    inference(subsumption_resolution,[],[f166,f86])).

fof(f166,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f202,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)),X0) ),
    inference(subsumption_resolution,[],[f201,f86])).

fof(f201,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f199,f41])).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | r1_tarski(k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f123,f45])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | r1_tarski(k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X3)),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f120,f53])).

fof(f120,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k2_funct_1(X2))
      | r1_tarski(k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X3)),X3)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (18570)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (18577)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (18562)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (18580)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (18579)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (18564)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (18577)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 1.31/0.55  % (18561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f1004,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(subsumption_resolution,[],[f1003,f104])).
% 1.31/0.55  fof(f104,plain,(
% 1.31/0.55    v5_relat_1(sK3,sK1)),
% 1.31/0.55    inference(resolution,[],[f69,f50])).
% 1.31/0.55  fof(f50,plain,(
% 1.31/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f19,plain,(
% 1.31/0.55    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.31/0.55    inference(flattening,[],[f18])).
% 1.31/0.55  fof(f18,plain,(
% 1.31/0.55    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.31/0.55    inference(ennf_transformation,[],[f17])).
% 1.31/0.55  fof(f17,negated_conjecture,(
% 1.31/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.31/0.55    inference(negated_conjecture,[],[f16])).
% 1.31/0.55  fof(f16,conjecture,(
% 1.31/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 1.31/0.55  fof(f69,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f34])).
% 1.31/0.55  fof(f34,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(ennf_transformation,[],[f10])).
% 1.31/0.55  fof(f10,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.31/0.55  fof(f1003,plain,(
% 1.31/0.55    ~v5_relat_1(sK3,sK1)),
% 1.31/0.55    inference(forward_demodulation,[],[f1002,f911])).
% 1.31/0.55  fof(f911,plain,(
% 1.31/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),sK2)),
% 1.31/0.55    inference(backward_demodulation,[],[f387,f894])).
% 1.31/0.55  fof(f894,plain,(
% 1.31/0.55    sK2 = k2_relat_1(sK4)),
% 1.31/0.55    inference(subsumption_resolution,[],[f893,f87])).
% 1.31/0.55  fof(f87,plain,(
% 1.31/0.55    v1_relat_1(sK3)),
% 1.31/0.55    inference(resolution,[],[f65,f50])).
% 1.31/0.55  fof(f65,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f31])).
% 1.31/0.55  fof(f31,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(ennf_transformation,[],[f9])).
% 1.31/0.55  fof(f9,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.31/0.55  fof(f893,plain,(
% 1.31/0.55    sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK3)),
% 1.31/0.55    inference(subsumption_resolution,[],[f888,f103])).
% 1.31/0.55  fof(f103,plain,(
% 1.31/0.55    v5_relat_1(sK4,sK2)),
% 1.31/0.55    inference(resolution,[],[f69,f43])).
% 1.31/0.55  fof(f43,plain,(
% 1.31/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f888,plain,(
% 1.31/0.55    ~v5_relat_1(sK4,sK2) | sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK3)),
% 1.31/0.55    inference(superposition,[],[f116,f860])).
% 1.31/0.55  fof(f860,plain,(
% 1.31/0.55    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.31/0.55    inference(forward_demodulation,[],[f855,f818])).
% 1.31/0.55  fof(f818,plain,(
% 1.31/0.55    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.31/0.55    inference(backward_demodulation,[],[f44,f817])).
% 1.31/0.55  fof(f817,plain,(
% 1.31/0.55    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.31/0.55    inference(resolution,[],[f815,f50])).
% 1.31/0.55  fof(f815,plain,(
% 1.31/0.55    ( ! [X15,X16] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | k5_relat_1(sK3,sK4) = k1_partfun1(X15,X16,sK1,sK2,sK3,sK4)) )),
% 1.31/0.55    inference(resolution,[],[f666,f48])).
% 1.31/0.55  fof(f48,plain,(
% 1.31/0.55    v1_funct_1(sK3)),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f666,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(X0,sK4) = k1_partfun1(X1,X2,sK1,sK2,X0,sK4)) )),
% 1.31/0.55    inference(resolution,[],[f429,f43])).
% 1.31/0.55  fof(f429,plain,(
% 1.31/0.55    ( ! [X26,X24,X23,X25,X22] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~v1_funct_1(X22) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | k1_partfun1(X23,X24,X25,X26,X22,sK4) = k5_relat_1(X22,sK4)) )),
% 1.31/0.55    inference(resolution,[],[f76,f41])).
% 1.31/0.55  fof(f41,plain,(
% 1.31/0.55    v1_funct_1(sK4)),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f76,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f38])).
% 1.31/0.55  fof(f38,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.31/0.55    inference(flattening,[],[f37])).
% 1.31/0.55  fof(f37,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.31/0.55    inference(ennf_transformation,[],[f15])).
% 1.31/0.55  fof(f15,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.31/0.55  fof(f44,plain,(
% 1.31/0.55    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f855,plain,(
% 1.31/0.55    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.31/0.55    inference(resolution,[],[f829,f67])).
% 1.31/0.55  fof(f67,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f33])).
% 1.31/0.55  fof(f33,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(ennf_transformation,[],[f12])).
% 1.31/0.55  fof(f12,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.31/0.55  fof(f829,plain,(
% 1.31/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.31/0.55    inference(subsumption_resolution,[],[f828,f48])).
% 1.31/0.55  fof(f828,plain,(
% 1.31/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 1.31/0.55    inference(subsumption_resolution,[],[f827,f43])).
% 1.31/0.55  fof(f827,plain,(
% 1.31/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 1.31/0.55    inference(subsumption_resolution,[],[f826,f41])).
% 1.31/0.55  fof(f826,plain,(
% 1.31/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 1.31/0.55    inference(subsumption_resolution,[],[f820,f50])).
% 1.31/0.55  fof(f820,plain,(
% 1.31/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 1.31/0.55    inference(superposition,[],[f78,f817])).
% 1.31/0.55  fof(f78,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f40])).
% 1.31/0.55  fof(f40,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.31/0.55    inference(flattening,[],[f39])).
% 1.31/0.55  fof(f39,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.31/0.55    inference(ennf_transformation,[],[f14])).
% 1.31/0.55  fof(f14,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.31/0.55  fof(f116,plain,(
% 1.31/0.55    ( ! [X0] : (~v5_relat_1(sK4,k2_relat_1(k5_relat_1(X0,sK4))) | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(X0)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f113,f86])).
% 1.31/0.55  fof(f86,plain,(
% 1.31/0.55    v1_relat_1(sK4)),
% 1.31/0.55    inference(resolution,[],[f65,f43])).
% 1.31/0.55  fof(f113,plain,(
% 1.31/0.55    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_relat_1(X0) | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) | ~v5_relat_1(sK4,k2_relat_1(k5_relat_1(X0,sK4)))) )),
% 1.31/0.55    inference(resolution,[],[f51,f99])).
% 1.31/0.55  fof(f99,plain,(
% 1.31/0.55    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(sK4)) | k2_relat_1(sK4) = X1 | ~v5_relat_1(sK4,X1)) )),
% 1.31/0.55    inference(resolution,[],[f64,f93])).
% 1.31/0.55  fof(f93,plain,(
% 1.31/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(sK4),X0) | ~v5_relat_1(sK4,X0)) )),
% 1.31/0.55    inference(resolution,[],[f59,f86])).
% 1.31/0.55  fof(f59,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f26])).
% 1.31/0.55  fof(f26,plain,(
% 1.31/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.55    inference(ennf_transformation,[],[f2])).
% 1.31/0.55  fof(f2,axiom,(
% 1.31/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.31/0.55  fof(f64,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.31/0.55    inference(cnf_transformation,[],[f1])).
% 1.31/0.55  fof(f1,axiom,(
% 1.31/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.55  fof(f51,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f20])).
% 1.31/0.55  fof(f20,plain,(
% 1.31/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.55    inference(ennf_transformation,[],[f4])).
% 1.31/0.55  fof(f4,axiom,(
% 1.31/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.31/0.55  fof(f387,plain,(
% 1.31/0.55    sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))),
% 1.31/0.55    inference(forward_demodulation,[],[f384,f358])).
% 1.31/0.55  fof(f358,plain,(
% 1.31/0.55    sK1 = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))),
% 1.31/0.55    inference(backward_demodulation,[],[f157,f356])).
% 1.31/0.55  fof(f356,plain,(
% 1.31/0.55    sK1 = k1_relat_1(sK4)),
% 1.31/0.55    inference(backward_demodulation,[],[f143,f355])).
% 1.31/0.55  fof(f355,plain,(
% 1.31/0.55    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.31/0.55    inference(subsumption_resolution,[],[f354,f42])).
% 1.31/0.55  fof(f42,plain,(
% 1.31/0.55    v1_funct_2(sK4,sK1,sK2)),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f354,plain,(
% 1.31/0.55    sK1 = k1_relset_1(sK1,sK2,sK4) | ~v1_funct_2(sK4,sK1,sK2)),
% 1.31/0.55    inference(subsumption_resolution,[],[f352,f46])).
% 1.31/0.55  fof(f46,plain,(
% 1.31/0.55    k1_xboole_0 != sK2),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f352,plain,(
% 1.31/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4) | ~v1_funct_2(sK4,sK1,sK2)),
% 1.31/0.55    inference(resolution,[],[f75,f43])).
% 1.31/0.55  fof(f75,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f36])).
% 1.31/0.55  fof(f36,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(flattening,[],[f35])).
% 1.31/0.55  fof(f35,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(ennf_transformation,[],[f13])).
% 1.31/0.55  fof(f13,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.31/0.55  fof(f143,plain,(
% 1.31/0.55    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 1.31/0.55    inference(resolution,[],[f66,f43])).
% 1.31/0.55  fof(f66,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f32])).
% 1.31/0.55  fof(f32,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(ennf_transformation,[],[f11])).
% 1.31/0.55  fof(f11,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.31/0.55  fof(f157,plain,(
% 1.31/0.55    k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))),
% 1.31/0.55    inference(subsumption_resolution,[],[f156,f86])).
% 1.31/0.55  fof(f156,plain,(
% 1.31/0.55    ~v1_relat_1(sK4) | k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))),
% 1.31/0.55    inference(subsumption_resolution,[],[f154,f41])).
% 1.31/0.55  fof(f154,plain,(
% 1.31/0.55    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_relat_1(sK4) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4)))),
% 1.31/0.55    inference(resolution,[],[f57,f45])).
% 1.31/0.55  fof(f45,plain,(
% 1.31/0.55    v2_funct_1(sK4)),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f57,plain,(
% 1.31/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f25])).
% 1.31/0.55  fof(f25,plain,(
% 1.31/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.55    inference(flattening,[],[f24])).
% 1.31/0.55  fof(f24,plain,(
% 1.31/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.55    inference(ennf_transformation,[],[f8])).
% 1.31/0.55  fof(f8,axiom,(
% 1.31/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.31/0.55  fof(f384,plain,(
% 1.31/0.55    k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))),
% 1.31/0.55    inference(resolution,[],[f381,f86])).
% 1.31/0.55  fof(f381,plain,(
% 1.31/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0))) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f380,f86])).
% 1.31/0.55  fof(f380,plain,(
% 1.31/0.55    ( ! [X0] : (k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK4)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f378,f41])).
% 1.31/0.55  fof(f378,plain,(
% 1.31/0.55    ( ! [X0] : (k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) | ~v1_funct_1(sK4) | ~v1_relat_1(X0) | ~v1_relat_1(sK4)) )),
% 1.31/0.55    inference(resolution,[],[f136,f45])).
% 1.31/0.55  fof(f136,plain,(
% 1.31/0.55    ( ! [X2,X3] : (~v2_funct_1(X3) | k2_relat_1(k5_relat_1(X2,k2_funct_1(X3))) = k9_relat_1(k2_funct_1(X3),k2_relat_1(X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 1.31/0.55    inference(resolution,[],[f52,f53])).
% 1.31/0.55  fof(f53,plain,(
% 1.31/0.55    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f23])).
% 1.31/0.55  fof(f23,plain,(
% 1.31/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.55    inference(flattening,[],[f22])).
% 1.31/0.55  fof(f22,plain,(
% 1.31/0.55    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.55    inference(ennf_transformation,[],[f5])).
% 1.31/0.55  fof(f5,axiom,(
% 1.31/0.55    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.31/0.55  fof(f52,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f21])).
% 1.31/0.55  fof(f21,plain,(
% 1.31/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.55    inference(ennf_transformation,[],[f3])).
% 1.31/0.55  fof(f3,axiom,(
% 1.31/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.31/0.55  fof(f1002,plain,(
% 1.31/0.55    ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),sK2))),
% 1.31/0.55    inference(subsumption_resolution,[],[f998,f147])).
% 1.31/0.55  fof(f147,plain,(
% 1.31/0.55    sK1 != k2_relat_1(sK3)),
% 1.31/0.55    inference(superposition,[],[f47,f146])).
% 1.31/0.55  fof(f146,plain,(
% 1.31/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.31/0.55    inference(resolution,[],[f67,f50])).
% 1.31/0.55  fof(f47,plain,(
% 1.31/0.55    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f998,plain,(
% 1.31/0.55    sK1 = k2_relat_1(sK3) | ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),sK2))),
% 1.31/0.55    inference(backward_demodulation,[],[f873,f911])).
% 1.31/0.55  fof(f873,plain,(
% 1.31/0.55    ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),sK2)) | k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2)),
% 1.31/0.55    inference(forward_demodulation,[],[f870,f866])).
% 1.31/0.55  fof(f866,plain,(
% 1.31/0.55    k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),sK2)),
% 1.31/0.55    inference(backward_demodulation,[],[f839,f860])).
% 1.31/0.55  fof(f839,plain,(
% 1.31/0.55    k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4)))),
% 1.31/0.55    inference(resolution,[],[f825,f381])).
% 1.31/0.55  fof(f825,plain,(
% 1.31/0.55    v1_relat_1(k5_relat_1(sK3,sK4))),
% 1.31/0.55    inference(subsumption_resolution,[],[f824,f50])).
% 1.31/0.55  fof(f824,plain,(
% 1.31/0.55    v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.55    inference(subsumption_resolution,[],[f823,f48])).
% 1.31/0.55  fof(f823,plain,(
% 1.31/0.55    v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.55    inference(subsumption_resolution,[],[f822,f43])).
% 1.31/0.55  fof(f822,plain,(
% 1.31/0.55    v1_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.55    inference(subsumption_resolution,[],[f819,f41])).
% 1.31/0.55  fof(f819,plain,(
% 1.31/0.55    v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.55    inference(superposition,[],[f526,f817])).
% 1.31/0.55  fof(f526,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_relat_1(k1_partfun1(X1,X2,X4,X5,X0,X3)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.31/0.55    inference(resolution,[],[f78,f65])).
% 1.31/0.55  fof(f870,plain,(
% 1.31/0.55    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),sK2) | ~v5_relat_1(sK3,k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))))),
% 1.31/0.55    inference(backward_demodulation,[],[f847,f866])).
% 1.31/0.55  fof(f847,plain,(
% 1.31/0.55    ~v5_relat_1(sK3,k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4)))) | k2_relat_1(sK3) = k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4)))),
% 1.31/0.55    inference(forward_demodulation,[],[f845,f839])).
% 1.31/0.55  fof(f845,plain,(
% 1.31/0.55    k2_relat_1(sK3) = k2_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k2_funct_1(sK4))) | ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))))),
% 1.31/0.55    inference(backward_demodulation,[],[f215,f839])).
% 1.31/0.55  fof(f215,plain,(
% 1.31/0.55    ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4)))) | k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4)))),
% 1.31/0.55    inference(forward_demodulation,[],[f214,f138])).
% 1.31/0.55  fof(f138,plain,(
% 1.31/0.55    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))),
% 1.31/0.55    inference(resolution,[],[f134,f87])).
% 1.31/0.55  fof(f134,plain,(
% 1.31/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) )),
% 1.31/0.55    inference(resolution,[],[f52,f86])).
% 1.31/0.55  fof(f214,plain,(
% 1.31/0.55    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) | ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))))),
% 1.31/0.55    inference(forward_demodulation,[],[f208,f138])).
% 1.31/0.55  fof(f208,plain,(
% 1.31/0.55    k2_relat_1(sK3) = k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) | ~v5_relat_1(sK3,k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))))),
% 1.31/0.55    inference(resolution,[],[f203,f100])).
% 1.31/0.55  fof(f100,plain,(
% 1.31/0.55    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK3)) | k2_relat_1(sK3) = X2 | ~v5_relat_1(sK3,X2)) )),
% 1.31/0.55    inference(resolution,[],[f64,f94])).
% 1.31/0.55  fof(f94,plain,(
% 1.31/0.55    ( ! [X1] : (r1_tarski(k2_relat_1(sK3),X1) | ~v5_relat_1(sK3,X1)) )),
% 1.31/0.55    inference(resolution,[],[f59,f87])).
% 1.31/0.55  fof(f203,plain,(
% 1.31/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0)) )),
% 1.31/0.55    inference(forward_demodulation,[],[f202,f167])).
% 1.31/0.55  fof(f167,plain,(
% 1.31/0.55    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f166,f86])).
% 1.31/0.55  fof(f166,plain,(
% 1.31/0.55    ( ! [X0] : (~v1_relat_1(sK4) | k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f164,f41])).
% 1.31/0.55  fof(f164,plain,(
% 1.31/0.55    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) )),
% 1.31/0.55    inference(resolution,[],[f61,f45])).
% 1.31/0.55  fof(f61,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f30])).
% 1.31/0.55  fof(f30,plain,(
% 1.31/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.55    inference(flattening,[],[f29])).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.55    inference(ennf_transformation,[],[f7])).
% 1.31/0.55  fof(f7,axiom,(
% 1.31/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 1.31/0.55  fof(f202,plain,(
% 1.31/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)),X0)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f201,f86])).
% 1.31/0.55  fof(f201,plain,(
% 1.31/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)),X0) | ~v1_relat_1(sK4)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f199,f41])).
% 1.31/0.55  fof(f199,plain,(
% 1.31/0.55    ( ! [X0] : (~v1_funct_1(sK4) | r1_tarski(k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)),X0) | ~v1_relat_1(sK4)) )),
% 1.31/0.55    inference(resolution,[],[f123,f45])).
% 1.31/0.55  fof(f123,plain,(
% 1.31/0.55    ( ! [X2,X3] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | r1_tarski(k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X3)),X3) | ~v1_relat_1(X2)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f120,f53])).
% 1.31/0.55  fof(f120,plain,(
% 1.31/0.55    ( ! [X2,X3] : (~v1_relat_1(k2_funct_1(X2)) | r1_tarski(k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X3)),X3) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.31/0.55    inference(resolution,[],[f60,f54])).
% 1.31/0.55  fof(f54,plain,(
% 1.31/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f23])).
% 1.31/0.55  fof(f60,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f28])).
% 1.31/0.55  fof(f28,plain,(
% 1.31/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.55    inference(flattening,[],[f27])).
% 1.31/0.55  fof(f27,plain,(
% 1.31/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.55    inference(ennf_transformation,[],[f6])).
% 1.31/0.55  fof(f6,axiom,(
% 1.31/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.31/0.55  % SZS output end Proof for theBenchmark
% 1.31/0.55  % (18577)------------------------------
% 1.31/0.55  % (18577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (18577)Termination reason: Refutation
% 1.31/0.55  
% 1.31/0.55  % (18577)Memory used [KB]: 2686
% 1.31/0.55  % (18577)Time elapsed: 0.132 s
% 1.31/0.55  % (18577)------------------------------
% 1.31/0.55  % (18577)------------------------------
% 1.31/0.55  % (18557)Success in time 0.193 s
%------------------------------------------------------------------------------
