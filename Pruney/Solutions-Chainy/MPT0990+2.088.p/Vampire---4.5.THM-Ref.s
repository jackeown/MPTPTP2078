%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:43 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  196 (4440 expanded)
%              Number of leaves         :   19 ( 809 expanded)
%              Depth                    :   33
%              Number of atoms          :  648 (32995 expanded)
%              Number of equality atoms :  202 (10426 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2257,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2256,f56])).

fof(f56,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f2256,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f347,f2229])).

fof(f2229,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f2126,f2171])).

fof(f2171,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f2096,f2159])).

fof(f2159,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f2080,f2102])).

fof(f2102,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f2099,f331])).

fof(f331,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f329,f308])).

fof(f308,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f290,f51])).

fof(f51,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f290,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f329,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f289,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f289,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2099,plain,(
    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f1396,f2096])).

fof(f1396,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f706,f1365])).

fof(f1365,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1364,f905])).

fof(f905,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f902,f899])).

fof(f899,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f894,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f894,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f248,f59])).

fof(f248,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X10)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(subsumption_resolution,[],[f236,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f236,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(resolution,[],[f50,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f902,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f351,f899])).

fof(f351,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f349,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f349,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f52,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f1364,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1363,f50])).

fof(f1363,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1362,f48])).

fof(f1362,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1361,f59])).

fof(f1361,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1360,f57])).

fof(f1360,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f88,f899])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f706,plain,(
    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f702,f251])).

fof(f251,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f223,f98])).

fof(f98,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f223,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f75])).

fof(f702,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(sK2,sK3),X8) = k5_relat_1(sK2,k5_relat_1(sK3,X8)) ) ),
    inference(resolution,[],[f253,f289])).

fof(f253,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f223,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f2080,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f1784,f2068])).

fof(f2068,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f2067,f1411])).

fof(f1411,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f903,f1365])).

fof(f903,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f52,f899])).

fof(f2067,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f2066,f1409])).

fof(f1409,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f899,f1365])).

fof(f2066,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f2065,f59])).

fof(f2065,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f2064,f57])).

fof(f2064,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(resolution,[],[f244,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f244,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) ) ),
    inference(backward_demodulation,[],[f179,f224])).

fof(f224,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f50,f76])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f178,f50])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f166,f48])).

fof(f166,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f49,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f49,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f1784,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f281,f1783])).

fof(f1783,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1782,f48])).

fof(f1782,plain,
    ( ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1776,f223])).

fof(f1776,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f1767,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1767,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1766,f1549])).

fof(f1549,plain,(
    v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1516,f1475])).

fof(f1475,plain,(
    v1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f1366,f1365])).

fof(f1366,plain,(
    v1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f1364,f75])).

fof(f1516,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(resolution,[],[f1410,f387])).

fof(f387,plain,
    ( ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f386,f360])).

fof(f360,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f207,f289])).

fof(f207,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f205,f90])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f60])).

fof(f63,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f205,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f133,f204])).

fof(f204,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f203,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f203,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f202,f53])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f202,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f201,f51])).

fof(f201,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f200,f59])).

fof(f200,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f192,f57])).

fof(f192,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f58,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f133,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f129,f57])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
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
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f386,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f385,f90])).

fof(f385,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f384,f57])).

fof(f384,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f383,f289])).

fof(f383,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f380,f53])).

fof(f380,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(superposition,[],[f73,f362])).

fof(f362,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(backward_demodulation,[],[f330,f360])).

fof(f330,plain,(
    sK2 = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) ),
    inference(resolution,[],[f289,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f1410,plain,(
    v1_funct_1(k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f901,f1365])).

fof(f901,plain,(
    v1_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(backward_demodulation,[],[f577,f899])).

fof(f577,plain,(
    v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f575,f57])).

fof(f575,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    inference(resolution,[],[f250,f59])).

fof(f250,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ v1_funct_1(X16)
      | v1_funct_1(k1_partfun1(X17,X18,sK1,sK0,X16,sK3)) ) ),
    inference(subsumption_resolution,[],[f238,f48])).

fof(f238,plain,(
    ! [X17,X18,X16] :
      ( ~ v1_funct_1(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ v1_funct_1(sK3)
      | v1_funct_1(k1_partfun1(X17,X18,sK1,sK0,X16,sK3)) ) ),
    inference(resolution,[],[f50,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1766,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f1765,f1409])).

fof(f1765,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1764,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f1764,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1763,f50])).

fof(f1763,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1762,f48])).

fof(f1762,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f221,f49])).

fof(f221,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X6,sK1,X7)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f220,f51])).

fof(f220,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f219,f59])).

fof(f219,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f198,f57])).

fof(f198,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(resolution,[],[f58,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f281,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) ),
    inference(resolution,[],[f251,f93])).

fof(f2096,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2089,f1767])).

fof(f2089,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f2073])).

fof(f2073,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f246,f2068])).

fof(f246,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f174,f224])).

fof(f174,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f173,f54])).

fof(f173,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f172,f50])).

fof(f172,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f164,f48])).

fof(f164,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f49,f77])).

fof(f2126,plain,(
    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f565,f2074])).

fof(f2074,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f265,f2068])).

fof(f265,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) ),
    inference(resolution,[],[f223,f92])).

fof(f565,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f562,f204])).

fof(f562,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f557,f315])).

fof(f315,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f289,f136])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f57,f67])).

fof(f557,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(sK3,sK2),X8) = k5_relat_1(sK3,k5_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f252,f289])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f223,f66])).

fof(f347,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f346,f310])).

fof(f310,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f309,f289])).

fof(f309,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f134,f308])).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f130,f57])).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f53,f69])).

fof(f346,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) ),
    inference(resolution,[],[f315,f93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (22997)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (23007)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (22998)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (23000)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (23008)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (23015)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (23012)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (22994)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (23009)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (23004)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (23002)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (23001)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (23016)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (22999)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (23018)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23017)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (23019)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (22992)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (22995)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (23010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (22991)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (22990)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (23011)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (22993)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (23005)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (23003)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (23014)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (23013)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.57  % (22996)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.57  % (23006)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.57  % (23006)Refutation not found, incomplete strategy% (23006)------------------------------
% 1.57/0.57  % (23006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (23006)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (23006)Memory used [KB]: 10746
% 1.57/0.57  % (23006)Time elapsed: 0.167 s
% 1.57/0.57  % (23006)------------------------------
% 1.57/0.57  % (23006)------------------------------
% 1.76/0.60  % (23007)Refutation found. Thanks to Tanya!
% 1.76/0.60  % SZS status Theorem for theBenchmark
% 1.76/0.62  % SZS output start Proof for theBenchmark
% 1.76/0.62  fof(f2257,plain,(
% 1.76/0.62    $false),
% 1.76/0.62    inference(subsumption_resolution,[],[f2256,f56])).
% 1.76/0.62  fof(f56,plain,(
% 1.76/0.62    sK3 != k2_funct_1(sK2)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f22,plain,(
% 1.76/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.76/0.62    inference(flattening,[],[f21])).
% 1.76/0.62  fof(f21,plain,(
% 1.76/0.62    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.76/0.62    inference(ennf_transformation,[],[f20])).
% 1.76/0.62  fof(f20,negated_conjecture,(
% 1.76/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.62    inference(negated_conjecture,[],[f19])).
% 1.76/0.62  fof(f19,conjecture,(
% 1.76/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.76/0.62  fof(f2256,plain,(
% 1.76/0.62    sK3 = k2_funct_1(sK2)),
% 1.76/0.62    inference(backward_demodulation,[],[f347,f2229])).
% 1.76/0.62  fof(f2229,plain,(
% 1.76/0.62    sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))),
% 1.76/0.62    inference(backward_demodulation,[],[f2126,f2171])).
% 1.76/0.62  fof(f2171,plain,(
% 1.76/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.76/0.62    inference(backward_demodulation,[],[f2096,f2159])).
% 1.76/0.62  fof(f2159,plain,(
% 1.76/0.62    sK2 = k2_funct_1(sK3)),
% 1.76/0.62    inference(forward_demodulation,[],[f2080,f2102])).
% 1.76/0.62  fof(f2102,plain,(
% 1.76/0.62    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 1.76/0.62    inference(forward_demodulation,[],[f2099,f331])).
% 1.76/0.62  fof(f331,plain,(
% 1.76/0.62    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 1.76/0.62    inference(forward_demodulation,[],[f329,f308])).
% 1.76/0.62  fof(f308,plain,(
% 1.76/0.62    sK1 = k2_relat_1(sK2)),
% 1.76/0.62    inference(forward_demodulation,[],[f290,f51])).
% 1.76/0.62  fof(f51,plain,(
% 1.76/0.62    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f290,plain,(
% 1.76/0.62    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.76/0.62    inference(resolution,[],[f59,f76])).
% 1.76/0.62  fof(f76,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f35])).
% 1.76/0.62  fof(f35,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(ennf_transformation,[],[f10])).
% 1.76/0.62  fof(f10,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.76/0.62  fof(f59,plain,(
% 1.76/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f329,plain,(
% 1.76/0.62    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 1.76/0.62    inference(resolution,[],[f289,f92])).
% 1.76/0.62  fof(f92,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.76/0.62    inference(definition_unfolding,[],[f64,f60])).
% 1.76/0.62  fof(f60,plain,(
% 1.76/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f15])).
% 1.76/0.62  fof(f15,axiom,(
% 1.76/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.76/0.62  fof(f64,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f23])).
% 1.76/0.62  fof(f23,plain,(
% 1.76/0.62    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f4])).
% 1.76/0.62  fof(f4,axiom,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.76/0.62  fof(f289,plain,(
% 1.76/0.62    v1_relat_1(sK2)),
% 1.76/0.62    inference(resolution,[],[f59,f75])).
% 1.76/0.62  fof(f75,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f34])).
% 1.76/0.62  fof(f34,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(ennf_transformation,[],[f9])).
% 1.76/0.62  fof(f9,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.76/0.62  fof(f2099,plain,(
% 1.76/0.62    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f1396,f2096])).
% 1.76/0.62  fof(f1396,plain,(
% 1.76/0.62    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f706,f1365])).
% 1.76/0.62  fof(f1365,plain,(
% 1.76/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.76/0.62    inference(resolution,[],[f1364,f905])).
% 1.76/0.62  fof(f905,plain,(
% 1.76/0.62    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.76/0.62    inference(forward_demodulation,[],[f902,f899])).
% 1.76/0.62  fof(f899,plain,(
% 1.76/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.76/0.62    inference(subsumption_resolution,[],[f894,f57])).
% 1.76/0.62  fof(f57,plain,(
% 1.76/0.62    v1_funct_1(sK2)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f894,plain,(
% 1.76/0.62    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.76/0.62    inference(resolution,[],[f248,f59])).
% 1.76/0.62  fof(f248,plain,(
% 1.76/0.62    ( ! [X12,X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(X10) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f236,f48])).
% 1.76/0.62  fof(f48,plain,(
% 1.76/0.62    v1_funct_1(sK3)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f236,plain,(
% 1.76/0.62    ( ! [X12,X10,X11] : (~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(sK3) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 1.76/0.62    inference(resolution,[],[f50,f86])).
% 1.76/0.62  fof(f86,plain,(
% 1.76/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f45])).
% 1.76/0.62  fof(f45,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.62    inference(flattening,[],[f44])).
% 1.76/0.62  fof(f44,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.62    inference(ennf_transformation,[],[f14])).
% 1.76/0.62  fof(f14,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.76/0.62  fof(f50,plain,(
% 1.76/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f902,plain,(
% 1.76/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.62    inference(backward_demodulation,[],[f351,f899])).
% 1.76/0.62  fof(f351,plain,(
% 1.76/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.62    inference(subsumption_resolution,[],[f349,f89])).
% 1.76/0.62  fof(f89,plain,(
% 1.76/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.62    inference(definition_unfolding,[],[f61,f60])).
% 1.76/0.62  fof(f61,plain,(
% 1.76/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f12])).
% 1.76/0.62  fof(f12,axiom,(
% 1.76/0.62    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.76/0.62  fof(f349,plain,(
% 1.76/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.62    inference(resolution,[],[f52,f85])).
% 1.76/0.62  fof(f85,plain,(
% 1.76/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f43])).
% 1.76/0.62  fof(f43,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(flattening,[],[f42])).
% 1.76/0.62  fof(f42,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.76/0.62    inference(ennf_transformation,[],[f11])).
% 1.76/0.62  fof(f11,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.76/0.62  fof(f52,plain,(
% 1.76/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f1364,plain,(
% 1.76/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1363,f50])).
% 1.76/0.62  fof(f1363,plain,(
% 1.76/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1362,f48])).
% 1.76/0.62  fof(f1362,plain,(
% 1.76/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1361,f59])).
% 1.76/0.62  fof(f1361,plain,(
% 1.76/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1360,f57])).
% 1.76/0.62  fof(f1360,plain,(
% 1.76/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.62    inference(superposition,[],[f88,f899])).
% 1.76/0.62  fof(f88,plain,(
% 1.76/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f47])).
% 1.76/0.62  fof(f47,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.62    inference(flattening,[],[f46])).
% 1.76/0.62  fof(f46,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.62    inference(ennf_transformation,[],[f13])).
% 1.76/0.62  fof(f13,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.76/0.62  fof(f706,plain,(
% 1.76/0.62    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 1.76/0.62    inference(resolution,[],[f702,f251])).
% 1.76/0.62  fof(f251,plain,(
% 1.76/0.62    v1_relat_1(k2_funct_1(sK3))),
% 1.76/0.62    inference(resolution,[],[f223,f98])).
% 1.76/0.62  fof(f98,plain,(
% 1.76/0.62    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 1.76/0.62    inference(resolution,[],[f48,f67])).
% 1.76/0.62  fof(f67,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f27])).
% 1.76/0.62  fof(f27,plain,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f26])).
% 1.76/0.62  fof(f26,plain,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f5])).
% 1.76/0.62  fof(f5,axiom,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.76/0.62  fof(f223,plain,(
% 1.76/0.62    v1_relat_1(sK3)),
% 1.76/0.62    inference(resolution,[],[f50,f75])).
% 1.76/0.62  fof(f702,plain,(
% 1.76/0.62    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(sK2,sK3),X8) = k5_relat_1(sK2,k5_relat_1(sK3,X8))) )),
% 1.76/0.62    inference(resolution,[],[f253,f289])).
% 1.76/0.62  fof(f253,plain,(
% 1.76/0.62    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 1.76/0.62    inference(resolution,[],[f223,f66])).
% 1.76/0.62  fof(f66,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f25])).
% 1.76/0.62  fof(f25,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f1])).
% 1.76/0.62  fof(f1,axiom,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.76/0.62  fof(f2080,plain,(
% 1.76/0.62    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f1784,f2068])).
% 1.76/0.62  fof(f2068,plain,(
% 1.76/0.62    sK0 = k2_relat_1(sK3)),
% 1.76/0.62    inference(subsumption_resolution,[],[f2067,f1411])).
% 1.76/0.62  fof(f1411,plain,(
% 1.76/0.62    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.76/0.62    inference(backward_demodulation,[],[f903,f1365])).
% 1.76/0.62  fof(f903,plain,(
% 1.76/0.62    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.62    inference(backward_demodulation,[],[f52,f899])).
% 1.76/0.62  fof(f2067,plain,(
% 1.76/0.62    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3)),
% 1.76/0.62    inference(forward_demodulation,[],[f2066,f1409])).
% 1.76/0.62  fof(f1409,plain,(
% 1.76/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.62    inference(backward_demodulation,[],[f899,f1365])).
% 1.76/0.62  fof(f2066,plain,(
% 1.76/0.62    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f2065,f59])).
% 1.76/0.62  fof(f2065,plain,(
% 1.76/0.62    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f2064,f57])).
% 1.76/0.62  fof(f2064,plain,(
% 1.76/0.62    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.62    inference(resolution,[],[f244,f58])).
% 1.76/0.62  fof(f58,plain,(
% 1.76/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f244,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))) )),
% 1.76/0.62    inference(backward_demodulation,[],[f179,f224])).
% 1.76/0.62  fof(f224,plain,(
% 1.76/0.62    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.76/0.62    inference(resolution,[],[f50,f76])).
% 1.76/0.62  fof(f179,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f178,f50])).
% 1.76/0.62  fof(f178,plain,(
% 1.76/0.62    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f166,f48])).
% 1.76/0.62  fof(f166,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 1.76/0.62    inference(resolution,[],[f49,f79])).
% 1.76/0.62  fof(f79,plain,(
% 1.76/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f39])).
% 1.76/0.62  fof(f39,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.62    inference(flattening,[],[f38])).
% 1.76/0.62  fof(f38,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.62    inference(ennf_transformation,[],[f16])).
% 1.76/0.62  fof(f16,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.76/0.62  fof(f49,plain,(
% 1.76/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f1784,plain,(
% 1.76/0.62    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f281,f1783])).
% 1.76/0.62  fof(f1783,plain,(
% 1.76/0.62    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1782,f48])).
% 1.76/0.62  fof(f1782,plain,(
% 1.76/0.62    ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1776,f223])).
% 1.76/0.62  fof(f1776,plain,(
% 1.76/0.62    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.76/0.62    inference(resolution,[],[f1767,f69])).
% 1.76/0.62  fof(f69,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f29])).
% 1.76/0.62  fof(f29,plain,(
% 1.76/0.62    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f28])).
% 1.76/0.62  fof(f28,plain,(
% 1.76/0.62    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f7])).
% 1.76/0.62  fof(f7,axiom,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.76/0.62  fof(f1767,plain,(
% 1.76/0.62    v2_funct_1(sK3)),
% 1.76/0.62    inference(subsumption_resolution,[],[f1766,f1549])).
% 1.76/0.62  fof(f1549,plain,(
% 1.76/0.62    v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f1516,f1475])).
% 1.76/0.62  fof(f1475,plain,(
% 1.76/0.62    v1_relat_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(forward_demodulation,[],[f1366,f1365])).
% 1.76/0.62  fof(f1366,plain,(
% 1.76/0.62    v1_relat_1(k5_relat_1(sK2,sK3))),
% 1.76/0.62    inference(resolution,[],[f1364,f75])).
% 1.76/0.62  fof(f1516,plain,(
% 1.76/0.62    ~v1_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(resolution,[],[f1410,f387])).
% 1.76/0.62  fof(f387,plain,(
% 1.76/0.62    ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f386,f360])).
% 1.76/0.62  fof(f360,plain,(
% 1.76/0.62    sK0 = k1_relat_1(sK2)),
% 1.76/0.62    inference(resolution,[],[f207,f289])).
% 1.76/0.62  fof(f207,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 1.76/0.62    inference(forward_demodulation,[],[f205,f90])).
% 1.76/0.62  fof(f90,plain,(
% 1.76/0.62    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.76/0.62    inference(definition_unfolding,[],[f63,f60])).
% 1.76/0.62  fof(f63,plain,(
% 1.76/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f2])).
% 1.76/0.62  fof(f2,axiom,(
% 1.76/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.76/0.62  fof(f205,plain,(
% 1.76/0.62    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2)),
% 1.76/0.62    inference(backward_demodulation,[],[f133,f204])).
% 1.76/0.62  fof(f204,plain,(
% 1.76/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f203,f55])).
% 1.76/0.62  fof(f55,plain,(
% 1.76/0.62    k1_xboole_0 != sK1),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f203,plain,(
% 1.76/0.62    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f202,f53])).
% 1.76/0.62  fof(f53,plain,(
% 1.76/0.62    v2_funct_1(sK2)),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f202,plain,(
% 1.76/0.62    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f201,f51])).
% 1.76/0.62  fof(f201,plain,(
% 1.76/0.62    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f200,f59])).
% 1.76/0.62  fof(f200,plain,(
% 1.76/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f192,f57])).
% 1.76/0.62  fof(f192,plain,(
% 1.76/0.62    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.62    inference(resolution,[],[f58,f77])).
% 1.76/0.62  fof(f77,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f37])).
% 1.76/0.62  fof(f37,plain,(
% 1.76/0.62    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.62    inference(flattening,[],[f36])).
% 1.76/0.62  fof(f36,plain,(
% 1.76/0.62    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.62    inference(ennf_transformation,[],[f18])).
% 1.76/0.62  fof(f18,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.76/0.62  fof(f133,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.76/0.62    inference(subsumption_resolution,[],[f129,f57])).
% 1.76/0.62  fof(f129,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.76/0.62    inference(resolution,[],[f53,f72])).
% 1.76/0.62  fof(f72,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f31])).
% 1.76/0.62  fof(f31,plain,(
% 1.76/0.62    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f30])).
% 1.76/0.62  fof(f30,plain,(
% 1.76/0.62    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f8])).
% 1.76/0.62  fof(f8,axiom,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.76/0.62  fof(f386,plain,(
% 1.76/0.62    sK0 != k1_relat_1(sK2) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(forward_demodulation,[],[f385,f90])).
% 1.76/0.62  fof(f385,plain,(
% 1.76/0.62    ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f384,f57])).
% 1.76/0.62  fof(f384,plain,(
% 1.76/0.62    ~v1_funct_1(sK2) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f383,f289])).
% 1.76/0.62  fof(f383,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(subsumption_resolution,[],[f380,f53])).
% 1.76/0.62  fof(f380,plain,(
% 1.76/0.62    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(k6_partfun1(sK0)) | k1_relat_1(sK2) != k2_relat_1(k6_partfun1(sK0)) | v2_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(superposition,[],[f73,f362])).
% 1.76/0.62  fof(f362,plain,(
% 1.76/0.62    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 1.76/0.62    inference(backward_demodulation,[],[f330,f360])).
% 1.76/0.62  fof(f330,plain,(
% 1.76/0.62    sK2 = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2)),
% 1.76/0.62    inference(resolution,[],[f289,f93])).
% 1.76/0.62  fof(f93,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.76/0.62    inference(definition_unfolding,[],[f65,f60])).
% 1.76/0.62  fof(f65,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f24])).
% 1.76/0.62  fof(f24,plain,(
% 1.76/0.62    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f3])).
% 1.76/0.62  fof(f3,axiom,(
% 1.76/0.62    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.76/0.62  fof(f73,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f33])).
% 1.76/0.62  fof(f33,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f32])).
% 1.76/0.62  fof(f32,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f6])).
% 1.76/0.62  fof(f6,axiom,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.76/0.62  fof(f1410,plain,(
% 1.76/0.62    v1_funct_1(k6_partfun1(sK0))),
% 1.76/0.62    inference(backward_demodulation,[],[f901,f1365])).
% 1.76/0.62  fof(f901,plain,(
% 1.76/0.62    v1_funct_1(k5_relat_1(sK2,sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f577,f899])).
% 1.76/0.62  fof(f577,plain,(
% 1.76/0.62    v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f575,f57])).
% 1.76/0.62  fof(f575,plain,(
% 1.76/0.62    ~v1_funct_1(sK2) | v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))),
% 1.76/0.62    inference(resolution,[],[f250,f59])).
% 1.76/0.62  fof(f250,plain,(
% 1.76/0.62    ( ! [X17,X18,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | ~v1_funct_1(X16) | v1_funct_1(k1_partfun1(X17,X18,sK1,sK0,X16,sK3))) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f238,f48])).
% 1.76/0.62  fof(f238,plain,(
% 1.76/0.62    ( ! [X17,X18,X16] : (~v1_funct_1(X16) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | ~v1_funct_1(sK3) | v1_funct_1(k1_partfun1(X17,X18,sK1,sK0,X16,sK3))) )),
% 1.76/0.62    inference(resolution,[],[f50,f87])).
% 1.76/0.62  fof(f87,plain,(
% 1.76/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f47])).
% 1.76/0.62  fof(f1766,plain,(
% 1.76/0.62    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3)),
% 1.76/0.62    inference(forward_demodulation,[],[f1765,f1409])).
% 1.76/0.62  fof(f1765,plain,(
% 1.76/0.62    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 1.76/0.62    inference(subsumption_resolution,[],[f1764,f54])).
% 1.76/0.62  fof(f54,plain,(
% 1.76/0.62    k1_xboole_0 != sK0),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f1764,plain,(
% 1.76/0.62    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 1.76/0.62    inference(subsumption_resolution,[],[f1763,f50])).
% 1.76/0.62  fof(f1763,plain,(
% 1.76/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 1.76/0.62    inference(subsumption_resolution,[],[f1762,f48])).
% 1.76/0.62  fof(f1762,plain,(
% 1.76/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 1.76/0.62    inference(resolution,[],[f221,f49])).
% 1.76/0.62  fof(f221,plain,(
% 1.76/0.62    ( ! [X6,X7] : (~v1_funct_2(X6,sK1,X7) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f220,f51])).
% 1.76/0.62  fof(f220,plain,(
% 1.76/0.62    ( ! [X6,X7] : (~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f219,f59])).
% 1.76/0.62  fof(f219,plain,(
% 1.76/0.62    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f198,f57])).
% 1.76/0.62  fof(f198,plain,(
% 1.76/0.62    ( ! [X6,X7] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 1.76/0.62    inference(resolution,[],[f58,f83])).
% 1.76/0.62  fof(f83,plain,(
% 1.76/0.62    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f41])).
% 1.76/0.62  fof(f41,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.76/0.62    inference(flattening,[],[f40])).
% 1.76/0.62  fof(f40,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.76/0.62    inference(ennf_transformation,[],[f17])).
% 1.76/0.62  fof(f17,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.76/0.62  fof(f281,plain,(
% 1.76/0.62    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))),
% 1.76/0.62    inference(resolution,[],[f251,f93])).
% 1.76/0.62  fof(f2096,plain,(
% 1.76/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f2089,f1767])).
% 1.76/0.62  fof(f2089,plain,(
% 1.76/0.62    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(trivial_inequality_removal,[],[f2073])).
% 1.76/0.62  fof(f2073,plain,(
% 1.76/0.62    sK0 != sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f246,f2068])).
% 1.76/0.62  fof(f246,plain,(
% 1.76/0.62    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(backward_demodulation,[],[f174,f224])).
% 1.76/0.62  fof(f174,plain,(
% 1.76/0.62    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f173,f54])).
% 1.76/0.62  fof(f173,plain,(
% 1.76/0.62    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f172,f50])).
% 1.76/0.62  fof(f172,plain,(
% 1.76/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(subsumption_resolution,[],[f164,f48])).
% 1.76/0.62  fof(f164,plain,(
% 1.76/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.76/0.62    inference(resolution,[],[f49,f77])).
% 1.76/0.62  fof(f2126,plain,(
% 1.76/0.62    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2))),
% 1.76/0.62    inference(backward_demodulation,[],[f565,f2074])).
% 1.76/0.62  fof(f2074,plain,(
% 1.76/0.62    sK3 = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.76/0.62    inference(backward_demodulation,[],[f265,f2068])).
% 1.76/0.62  fof(f265,plain,(
% 1.76/0.62    sK3 = k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3)))),
% 1.76/0.62    inference(resolution,[],[f223,f92])).
% 1.76/0.62  fof(f565,plain,(
% 1.76/0.62    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.76/0.62    inference(forward_demodulation,[],[f562,f204])).
% 1.76/0.62  fof(f562,plain,(
% 1.76/0.62    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.76/0.62    inference(resolution,[],[f557,f315])).
% 1.76/0.62  fof(f315,plain,(
% 1.76/0.62    v1_relat_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(resolution,[],[f289,f136])).
% 1.76/0.62  fof(f136,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(resolution,[],[f57,f67])).
% 1.76/0.62  fof(f557,plain,(
% 1.76/0.62    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(sK3,sK2),X8) = k5_relat_1(sK3,k5_relat_1(sK2,X8))) )),
% 1.76/0.62    inference(resolution,[],[f252,f289])).
% 1.76/0.62  fof(f252,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1))) )),
% 1.76/0.62    inference(resolution,[],[f223,f66])).
% 1.76/0.62  fof(f347,plain,(
% 1.76/0.62    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))),
% 1.76/0.62    inference(forward_demodulation,[],[f346,f310])).
% 1.76/0.62  fof(f310,plain,(
% 1.76/0.62    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f309,f289])).
% 1.76/0.62  fof(f309,plain,(
% 1.76/0.62    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.76/0.62    inference(backward_demodulation,[],[f134,f308])).
% 1.76/0.62  fof(f134,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f130,f57])).
% 1.76/0.62  fof(f130,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(resolution,[],[f53,f69])).
% 1.76/0.62  fof(f346,plain,(
% 1.76/0.62    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))),
% 1.76/0.62    inference(resolution,[],[f315,f93])).
% 1.76/0.62  % SZS output end Proof for theBenchmark
% 1.76/0.62  % (23007)------------------------------
% 1.76/0.62  % (23007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (23007)Termination reason: Refutation
% 1.76/0.62  
% 1.76/0.62  % (23007)Memory used [KB]: 2558
% 1.76/0.62  % (23007)Time elapsed: 0.193 s
% 1.76/0.62  % (23007)------------------------------
% 1.76/0.62  % (23007)------------------------------
% 1.76/0.63  % (22988)Success in time 0.266 s
%------------------------------------------------------------------------------
