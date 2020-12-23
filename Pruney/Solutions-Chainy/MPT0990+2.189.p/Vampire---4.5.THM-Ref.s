%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:01 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  196 (3785 expanded)
%              Number of leaves         :   20 (1184 expanded)
%              Depth                    :   26
%              Number of atoms          :  739 (36807 expanded)
%              Number of equality atoms :  266 (12606 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f690,plain,(
    $false ),
    inference(subsumption_resolution,[],[f689,f380])).

fof(f380,plain,(
    k6_relat_1(sK1) != k5_relat_1(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( sK0 != sK0
    | k6_relat_1(sK1) != k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f307,f368])).

fof(f368,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f363,f68])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f363,plain,(
    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f68,f351])).

fof(f351,plain,(
    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f350])).

fof(f350,plain,
    ( sK1 != sK1
    | k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(superposition,[],[f221,f240])).

fof(f240,plain,(
    sK1 = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(forward_demodulation,[],[f237,f145])).

fof(f145,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f142,f57])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f142,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f78,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f237,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(resolution,[],[f146,f78])).

fof(f146,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(backward_demodulation,[],[f140,f145])).

fof(f140,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f138,f129])).

fof(f129,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f126,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f126,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f221,plain,
    ( sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f220,f179])).

fof(f179,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f178,f51])).

fof(f178,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f104])).

fof(f104,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f61,f101])).

fof(f101,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f70,f63])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f177,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f53])).

fof(f176,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f175,f57])).

fof(f175,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f173,f59])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f173,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | o_0_0_xboole_0 = X1
      | ~ v1_funct_1(X2) ) ),
    inference(backward_demodulation,[],[f99,f101])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f79,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f220,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(subsumption_resolution,[],[f219,f51])).

fof(f219,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f218,f104])).

fof(f218,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f217,f146])).

fof(f217,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f210,f59])).

fof(f210,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f147,f111])).

fof(f147,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f133,f145])).

fof(f133,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f131,f129])).

fof(f131,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f307,plain,
    ( k6_relat_1(sK1) != k5_relat_1(sK3,sK2)
    | sK0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f265,f293])).

fof(f293,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f143,f292])).

fof(f292,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f291,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f291,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f290,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f290,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f289,f96])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f58,f64])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f289,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f187,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK1,sK0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f186,f51])).

fof(f186,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f184,f53])).

fof(f184,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f100,f52])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f81,f64])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f143,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f78,f56])).

fof(f265,plain,
    ( k6_relat_1(sK1) != k5_relat_1(sK3,sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f264,f145])).

fof(f264,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f263,f129])).

fof(f263,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f262,f62])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f262,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f260,f59])).

fof(f260,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = sK3
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f157,f51])).

fof(f157,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k2_relat_1(sK3) != k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | sK3 = k2_funct_1(X1)
      | k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f154,f130])).

fof(f130,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f127,f76])).

fof(f127,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f71,f56])).

fof(f154,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1)
      | k2_relat_1(sK3) != k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | sK3 = k2_funct_1(X1)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f75,f54])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f689,plain,(
    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f648,f686])).

fof(f686,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f681,f598])).

fof(f598,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f579,f66])).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f579,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f470,f569])).

fof(f569,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f507,f473])).

fof(f473,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f471,f467])).

fof(f467,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f394,f56])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) ) ),
    inference(resolution,[],[f269,f53])).

fof(f269,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(X0,X1,X2,X3,sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f159,f51])).

fof(f159,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f88,f54])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f471,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f150,f467])).

fof(f150,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f149,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f67,f64])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f149,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f86,f96])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f507,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f505,f467])).

fof(f505,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f400,f56])).

fof(f400,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f273,f53])).

fof(f273,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f161,f51])).

fof(f161,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f90,f54])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f470,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f285,f467])).

fof(f285,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f284,f51])).

fof(f284,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f283,f53])).

fof(f283,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f281,f57])).

fof(f281,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f202,f52])).

fof(f202,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,sK1)
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f201,f54])).

fof(f201,plain,(
    ! [X2,X3] :
      ( v2_funct_1(sK3)
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f200,f103])).

fof(f103,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f60,f101])).

fof(f60,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f47])).

fof(f200,plain,(
    ! [X2,X3] :
      ( v2_funct_1(sK3)
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | o_0_0_xboole_0 = sK0
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f199,f56])).

fof(f199,plain,(
    ! [X2,X3] :
      ( v2_funct_1(sK3)
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | o_0_0_xboole_0 = sK0
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f107,f55])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | v2_funct_1(X4)
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | o_0_0_xboole_0 = X2
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(backward_demodulation,[],[f84,f101])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f681,plain,
    ( ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f678])).

fof(f678,plain,
    ( sK1 != sK1
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f597,f657])).

fof(f657,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f652,f68])).

fof(f652,plain,(
    k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f68,f647])).

fof(f647,plain,(
    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f646,f598])).

fof(f646,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f311,f643])).

fof(f643,plain,(
    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(resolution,[],[f598,f320])).

fof(f320,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f304,f103])).

fof(f304,plain,
    ( o_0_0_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f246,f293])).

fof(f246,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = k2_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f234,f241])).

fof(f241,plain,(
    k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    inference(resolution,[],[f141,f78])).

fof(f141,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f139,f130])).

fof(f139,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f54])).

fof(f234,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | o_0_0_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f233,f54])).

fof(f233,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | o_0_0_xboole_0 = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f225,f141])).

fof(f225,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | o_0_0_xboole_0 = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f134,f111])).

fof(f134,plain,(
    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f132,f130])).

fof(f132,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f54])).

fof(f311,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f298])).

fof(f298,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f183,f293])).

fof(f183,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | sK0 != k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f182,f143])).

fof(f182,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f181,f54])).

fof(f181,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f180,f103])).

fof(f180,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | o_0_0_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f174,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | o_0_0_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f111,f55])).

fof(f597,plain,
    ( ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f574])).

fof(f574,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f306,f569])).

fof(f306,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f255,f293])).

fof(f255,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f251,f130])).

fof(f251,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f156,f54])).

fof(f156,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f155,f145])).

fof(f155,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f153,f129])).

fof(f153,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f75,f51])).

fof(f648,plain,(
    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f643,f647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (3820)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (3844)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (3835)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (3825)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3826)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3827)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (3823)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (3834)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (3824)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (3821)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (3843)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (3836)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (3828)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (3830)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (3831)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (3845)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (3850)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (3840)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (3822)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (3848)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (3847)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3846)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (3849)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (3842)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (3836)Refutation not found, incomplete strategy% (3836)------------------------------
% 0.21/0.54  % (3836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3836)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3836)Memory used [KB]: 10746
% 0.21/0.54  % (3836)Time elapsed: 0.125 s
% 0.21/0.54  % (3836)------------------------------
% 0.21/0.54  % (3836)------------------------------
% 0.21/0.55  % (3837)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (3839)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (3841)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (3832)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (3833)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (3829)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.54/0.57  % (3827)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f690,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(subsumption_resolution,[],[f689,f380])).
% 1.54/0.57  fof(f380,plain,(
% 1.54/0.57    k6_relat_1(sK1) != k5_relat_1(sK3,sK2)),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f376])).
% 1.54/0.57  fof(f376,plain,(
% 1.54/0.57    sK0 != sK0 | k6_relat_1(sK1) != k5_relat_1(sK3,sK2)),
% 1.54/0.57    inference(backward_demodulation,[],[f307,f368])).
% 1.54/0.57  fof(f368,plain,(
% 1.54/0.57    sK0 = k1_relat_1(sK2)),
% 1.54/0.57    inference(forward_demodulation,[],[f363,f68])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.54/0.57  fof(f363,plain,(
% 1.54/0.57    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))),
% 1.54/0.57    inference(superposition,[],[f68,f351])).
% 1.54/0.57  fof(f351,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f350])).
% 1.54/0.57  fof(f350,plain,(
% 1.54/0.57    sK1 != sK1 | k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 1.54/0.57    inference(superposition,[],[f221,f240])).
% 1.54/0.57  fof(f240,plain,(
% 1.54/0.57    sK1 = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 1.54/0.57    inference(forward_demodulation,[],[f237,f145])).
% 1.54/0.57  fof(f145,plain,(
% 1.54/0.57    sK1 = k2_relat_1(sK2)),
% 1.54/0.57    inference(forward_demodulation,[],[f142,f57])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f46,f45])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.54/0.57    inference(flattening,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f21])).
% 1.54/0.57  fof(f21,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.54/0.57    inference(negated_conjecture,[],[f20])).
% 1.54/0.57  fof(f20,conjecture,(
% 1.54/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.54/0.57  fof(f142,plain,(
% 1.54/0.57    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f78,f53])).
% 1.54/0.57  fof(f53,plain,(
% 1.54/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f78,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f32])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.54/0.57  fof(f237,plain,(
% 1.54/0.57    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 1.54/0.57    inference(resolution,[],[f146,f78])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 1.54/0.57    inference(backward_demodulation,[],[f140,f145])).
% 1.54/0.57  fof(f140,plain,(
% 1.54/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.54/0.57    inference(subsumption_resolution,[],[f138,f129])).
% 1.54/0.57  fof(f129,plain,(
% 1.54/0.57    v1_relat_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f126,f76])).
% 1.54/0.57  fof(f76,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.54/0.57  fof(f126,plain,(
% 1.54/0.57    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.54/0.57    inference(resolution,[],[f71,f53])).
% 1.54/0.57  fof(f71,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f5])).
% 1.54/0.57  fof(f5,axiom,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.54/0.57  fof(f138,plain,(
% 1.54/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f74,f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    v1_funct_1(sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f74,plain,(
% 1.54/0.57    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,axiom,(
% 1.54/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.54/0.57  fof(f221,plain,(
% 1.54/0.57    sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 1.54/0.57    inference(forward_demodulation,[],[f220,f179])).
% 1.54/0.57  fof(f179,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.54/0.57    inference(subsumption_resolution,[],[f178,f51])).
% 1.54/0.57  fof(f178,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f177,f104])).
% 1.54/0.57  fof(f104,plain,(
% 1.54/0.57    o_0_0_xboole_0 != sK1),
% 1.54/0.57    inference(backward_demodulation,[],[f61,f101])).
% 1.54/0.57  fof(f101,plain,(
% 1.54/0.57    o_0_0_xboole_0 = k1_xboole_0),
% 1.54/0.57    inference(resolution,[],[f70,f63])).
% 1.54/0.57  fof(f63,plain,(
% 1.54/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 1.54/0.57    inference(cnf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.54/0.57  fof(f70,plain,(
% 1.54/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    k1_xboole_0 != sK1),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f177,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f176,f53])).
% 1.54/0.57  fof(f176,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f175,f57])).
% 1.54/0.57  fof(f175,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f173,f59])).
% 1.54/0.57  fof(f59,plain,(
% 1.54/0.57    v2_funct_1(sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f173,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f111,f52])).
% 1.54/0.57  fof(f52,plain,(
% 1.54/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f111,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | o_0_0_xboole_0 = X1 | ~v1_funct_1(X2)) )),
% 1.54/0.57    inference(backward_demodulation,[],[f99,f101])).
% 1.54/0.57  fof(f99,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.57    inference(forward_demodulation,[],[f79,f64])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f15])).
% 1.54/0.57  fof(f15,axiom,(
% 1.54/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.54/0.57  fof(f79,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.57    inference(flattening,[],[f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f18])).
% 1.54/0.57  fof(f18,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.54/0.57  fof(f220,plain,(
% 1.54/0.57    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f219,f51])).
% 1.54/0.57  fof(f219,plain,(
% 1.54/0.57    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f218,f104])).
% 1.54/0.57  fof(f218,plain,(
% 1.54/0.57    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f217,f146])).
% 1.54/0.57  fof(f217,plain,(
% 1.54/0.57    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f210,f59])).
% 1.54/0.57  fof(f210,plain,(
% 1.54/0.57    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | o_0_0_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f147,f111])).
% 1.54/0.57  fof(f147,plain,(
% 1.54/0.57    v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 1.54/0.57    inference(backward_demodulation,[],[f133,f145])).
% 1.54/0.57  fof(f133,plain,(
% 1.54/0.57    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.54/0.57    inference(subsumption_resolution,[],[f131,f129])).
% 1.54/0.57  fof(f131,plain,(
% 1.54/0.57    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f73,f51])).
% 1.54/0.57  fof(f73,plain,(
% 1.54/0.57    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f307,plain,(
% 1.54/0.57    k6_relat_1(sK1) != k5_relat_1(sK3,sK2) | sK0 != k1_relat_1(sK2)),
% 1.54/0.57    inference(backward_demodulation,[],[f265,f293])).
% 1.54/0.57  fof(f293,plain,(
% 1.54/0.57    sK0 = k2_relat_1(sK3)),
% 1.54/0.57    inference(backward_demodulation,[],[f143,f292])).
% 1.54/0.57  fof(f292,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f291,f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    v1_funct_1(sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f291,plain,(
% 1.54/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f290,f56])).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f290,plain,(
% 1.54/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f289,f96])).
% 1.54/0.57  fof(f96,plain,(
% 1.54/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.54/0.57    inference(forward_demodulation,[],[f58,f64])).
% 1.54/0.57  fof(f58,plain,(
% 1.54/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f289,plain,(
% 1.54/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(resolution,[],[f187,f55])).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    v1_funct_2(sK3,sK1,sK0)),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f187,plain,(
% 1.54/0.57    ( ! [X0] : (~v1_funct_2(X0,sK1,sK0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,X0) | ~v1_funct_1(X0)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f186,f51])).
% 1.54/0.57  fof(f186,plain,(
% 1.54/0.57    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f184,f53])).
% 1.54/0.57  fof(f184,plain,(
% 1.54/0.57    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.54/0.57    inference(resolution,[],[f100,f52])).
% 1.54/0.57  fof(f100,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.57    inference(forward_demodulation,[],[f81,f64])).
% 1.54/0.57  fof(f81,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.57    inference(flattening,[],[f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.54/0.57  fof(f143,plain,(
% 1.54/0.57    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 1.54/0.57    inference(resolution,[],[f78,f56])).
% 1.54/0.57  fof(f265,plain,(
% 1.54/0.57    k6_relat_1(sK1) != k5_relat_1(sK3,sK2) | k1_relat_1(sK2) != k2_relat_1(sK3)),
% 1.54/0.57    inference(forward_demodulation,[],[f264,f145])).
% 1.54/0.57  fof(f264,plain,(
% 1.54/0.57    k1_relat_1(sK2) != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f263,f129])).
% 1.54/0.57  fof(f263,plain,(
% 1.54/0.57    k1_relat_1(sK2) != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f262,f62])).
% 1.54/0.57  fof(f62,plain,(
% 1.54/0.57    k2_funct_1(sK2) != sK3),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f262,plain,(
% 1.54/0.57    k1_relat_1(sK2) != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f260,f59])).
% 1.54/0.57  fof(f260,plain,(
% 1.54/0.57    k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = sK3 | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f157,f51])).
% 1.54/0.57  fof(f157,plain,(
% 1.54/0.57    ( ! [X1] : (~v1_funct_1(X1) | k2_relat_1(sK3) != k1_relat_1(X1) | ~v2_funct_1(X1) | sK3 = k2_funct_1(X1) | k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f154,f130])).
% 1.54/0.57  fof(f130,plain,(
% 1.54/0.57    v1_relat_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f127,f76])).
% 1.54/0.57  fof(f127,plain,(
% 1.54/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.54/0.57    inference(resolution,[],[f71,f56])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    ( ! [X1] : (k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1) | k2_relat_1(sK3) != k1_relat_1(X1) | ~v2_funct_1(X1) | sK3 = k2_funct_1(X1) | ~v1_relat_1(sK3) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(resolution,[],[f75,f54])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | k2_funct_1(X0) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.54/0.57  fof(f689,plain,(
% 1.54/0.57    k6_relat_1(sK1) = k5_relat_1(sK3,sK2)),
% 1.54/0.57    inference(backward_demodulation,[],[f648,f686])).
% 1.54/0.57  fof(f686,plain,(
% 1.54/0.57    sK2 = k2_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f681,f598])).
% 1.54/0.57  fof(f598,plain,(
% 1.54/0.57    v2_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f579,f66])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.54/0.57  fof(f579,plain,(
% 1.54/0.57    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3)),
% 1.54/0.57    inference(backward_demodulation,[],[f470,f569])).
% 1.54/0.57  fof(f569,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.54/0.57    inference(resolution,[],[f507,f473])).
% 1.54/0.57  fof(f473,plain,(
% 1.54/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.54/0.57    inference(forward_demodulation,[],[f471,f467])).
% 1.54/0.57  fof(f467,plain,(
% 1.54/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.54/0.57    inference(resolution,[],[f394,f56])).
% 1.54/0.57  fof(f394,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3)) )),
% 1.54/0.57    inference(resolution,[],[f269,f53])).
% 1.54/0.57  fof(f269,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(X0,X1,X2,X3,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.54/0.57    inference(resolution,[],[f159,f51])).
% 1.54/0.57  fof(f159,plain,(
% 1.54/0.57    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.54/0.57    inference(resolution,[],[f88,f54])).
% 1.54/0.57  fof(f88,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f42])).
% 1.54/0.57  fof(f42,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.57    inference(flattening,[],[f41])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.57    inference(ennf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,axiom,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.54/0.57  fof(f471,plain,(
% 1.54/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.54/0.57    inference(backward_demodulation,[],[f150,f467])).
% 1.54/0.57  fof(f150,plain,(
% 1.54/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.54/0.57    inference(subsumption_resolution,[],[f149,f97])).
% 1.54/0.57  fof(f97,plain,(
% 1.54/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.57    inference(forward_demodulation,[],[f67,f64])).
% 1.54/0.57  fof(f67,plain,(
% 1.54/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.57    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.54/0.57    inference(pure_predicate_removal,[],[f13])).
% 1.54/0.57  fof(f13,axiom,(
% 1.54/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.54/0.57  fof(f149,plain,(
% 1.54/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.57    inference(resolution,[],[f86,f96])).
% 1.54/0.57  fof(f86,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f48])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(nnf_transformation,[],[f40])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(flattening,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.54/0.57    inference(ennf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.54/0.57  fof(f507,plain,(
% 1.54/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.57    inference(forward_demodulation,[],[f505,f467])).
% 1.54/0.57  fof(f505,plain,(
% 1.54/0.57    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.57    inference(resolution,[],[f400,f56])).
% 1.54/0.57  fof(f400,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 1.54/0.57    inference(resolution,[],[f273,f53])).
% 1.54/0.57  fof(f273,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.54/0.57    inference(resolution,[],[f161,f51])).
% 1.54/0.57  fof(f161,plain,(
% 1.54/0.57    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.54/0.57    inference(resolution,[],[f90,f54])).
% 1.54/0.57  fof(f90,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f44])).
% 1.54/0.57  fof(f44,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.57    inference(flattening,[],[f43])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.57    inference(ennf_transformation,[],[f12])).
% 1.54/0.57  fof(f12,axiom,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.54/0.57  fof(f470,plain,(
% 1.54/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 1.54/0.57    inference(backward_demodulation,[],[f285,f467])).
% 1.54/0.57  fof(f285,plain,(
% 1.54/0.57    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 1.54/0.57    inference(subsumption_resolution,[],[f284,f51])).
% 1.54/0.57  fof(f284,plain,(
% 1.54/0.57    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f283,f53])).
% 1.54/0.57  fof(f283,plain,(
% 1.54/0.57    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f281,f57])).
% 1.54/0.57  fof(f281,plain,(
% 1.54/0.57    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 1.54/0.57    inference(resolution,[],[f202,f52])).
% 1.54/0.57  fof(f202,plain,(
% 1.54/0.57    ( ! [X2,X3] : (~v1_funct_2(X3,X2,sK1) | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | v2_funct_1(sK3) | ~v1_funct_1(X3)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f201,f54])).
% 1.54/0.57  fof(f201,plain,(
% 1.54/0.57    ( ! [X2,X3] : (v2_funct_1(sK3) | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f200,f103])).
% 1.54/0.57  fof(f103,plain,(
% 1.54/0.57    o_0_0_xboole_0 != sK0),
% 1.54/0.57    inference(backward_demodulation,[],[f60,f101])).
% 1.54/0.57  fof(f60,plain,(
% 1.54/0.57    k1_xboole_0 != sK0),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f200,plain,(
% 1.54/0.57    ( ! [X2,X3] : (v2_funct_1(sK3) | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | o_0_0_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f199,f56])).
% 1.54/0.57  fof(f199,plain,(
% 1.54/0.57    ( ! [X2,X3] : (v2_funct_1(sK3) | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | o_0_0_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.54/0.57    inference(resolution,[],[f107,f55])).
% 1.54/0.57  fof(f107,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | v2_funct_1(X4) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | o_0_0_xboole_0 = X2 | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.54/0.57    inference(backward_demodulation,[],[f84,f101])).
% 1.54/0.57  fof(f84,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.54/0.57    inference(flattening,[],[f37])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.54/0.57    inference(ennf_transformation,[],[f17])).
% 1.54/0.57  fof(f17,axiom,(
% 1.54/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.54/0.57  fof(f681,plain,(
% 1.54/0.57    ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f678])).
% 1.54/0.57  fof(f678,plain,(
% 1.54/0.57    sK1 != sK1 | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 1.54/0.57    inference(backward_demodulation,[],[f597,f657])).
% 1.54/0.57  fof(f657,plain,(
% 1.54/0.57    sK1 = k1_relat_1(sK3)),
% 1.54/0.57    inference(forward_demodulation,[],[f652,f68])).
% 1.54/0.57  fof(f652,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1))),
% 1.54/0.57    inference(superposition,[],[f68,f647])).
% 1.54/0.57  fof(f647,plain,(
% 1.54/0.57    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))),
% 1.54/0.57    inference(subsumption_resolution,[],[f646,f598])).
% 1.54/0.57  fof(f646,plain,(
% 1.54/0.57    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3)),
% 1.54/0.57    inference(backward_demodulation,[],[f311,f643])).
% 1.54/0.57  fof(f643,plain,(
% 1.54/0.57    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))),
% 1.54/0.57    inference(resolution,[],[f598,f320])).
% 1.54/0.57  fof(f320,plain,(
% 1.54/0.57    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))),
% 1.54/0.57    inference(subsumption_resolution,[],[f304,f103])).
% 1.54/0.58  fof(f304,plain,(
% 1.54/0.58    o_0_0_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3)),
% 1.54/0.58    inference(backward_demodulation,[],[f246,f293])).
% 1.54/0.58  fof(f246,plain,(
% 1.54/0.58    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = k2_relat_1(sK3)),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f245])).
% 1.54/0.58  fof(f245,plain,(
% 1.54/0.58    k2_relat_1(sK3) != k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = k2_relat_1(sK3)),
% 1.54/0.58    inference(backward_demodulation,[],[f234,f241])).
% 1.54/0.58  fof(f241,plain,(
% 1.54/0.58    k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 1.54/0.58    inference(resolution,[],[f141,f78])).
% 1.54/0.58  fof(f141,plain,(
% 1.54/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 1.54/0.58    inference(subsumption_resolution,[],[f139,f130])).
% 1.54/0.58  fof(f139,plain,(
% 1.54/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 1.54/0.58    inference(resolution,[],[f74,f54])).
% 1.54/0.58  fof(f234,plain,(
% 1.54/0.58    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | o_0_0_xboole_0 = k2_relat_1(sK3)),
% 1.54/0.58    inference(subsumption_resolution,[],[f233,f54])).
% 1.54/0.58  fof(f233,plain,(
% 1.54/0.58    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | o_0_0_xboole_0 = k2_relat_1(sK3) | ~v1_funct_1(sK3)),
% 1.54/0.58    inference(subsumption_resolution,[],[f225,f141])).
% 1.54/0.58  fof(f225,plain,(
% 1.54/0.58    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | o_0_0_xboole_0 = k2_relat_1(sK3) | ~v1_funct_1(sK3)),
% 1.54/0.58    inference(resolution,[],[f134,f111])).
% 1.54/0.58  fof(f134,plain,(
% 1.54/0.58    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 1.54/0.58    inference(subsumption_resolution,[],[f132,f130])).
% 1.54/0.58  fof(f132,plain,(
% 1.54/0.58    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.54/0.58    inference(resolution,[],[f73,f54])).
% 1.54/0.58  fof(f311,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f298])).
% 1.54/0.58  fof(f298,plain,(
% 1.54/0.58    sK0 != sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.54/0.58    inference(backward_demodulation,[],[f183,f293])).
% 1.54/0.58  fof(f183,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | sK0 != k2_relat_1(sK3)),
% 1.54/0.58    inference(forward_demodulation,[],[f182,f143])).
% 1.54/0.58  fof(f182,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3)),
% 1.54/0.58    inference(subsumption_resolution,[],[f181,f54])).
% 1.54/0.58  fof(f181,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.54/0.58    inference(subsumption_resolution,[],[f180,f103])).
% 1.54/0.58  fof(f180,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | o_0_0_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.54/0.58    inference(subsumption_resolution,[],[f174,f56])).
% 1.54/0.58  fof(f174,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | o_0_0_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.54/0.58    inference(resolution,[],[f111,f55])).
% 1.54/0.58  fof(f597,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f574])).
% 1.54/0.58  fof(f574,plain,(
% 1.54/0.58    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.54/0.58    inference(backward_demodulation,[],[f306,f569])).
% 1.54/0.58  fof(f306,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.54/0.58    inference(backward_demodulation,[],[f255,f293])).
% 1.54/0.58  fof(f255,plain,(
% 1.54/0.58    k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.54/0.58    inference(subsumption_resolution,[],[f251,f130])).
% 1.54/0.58  fof(f251,plain,(
% 1.54/0.58    k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.54/0.58    inference(resolution,[],[f156,f54])).
% 1.54/0.58  fof(f156,plain,(
% 1.54/0.58    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f155,f145])).
% 1.54/0.58  fof(f155,plain,(
% 1.54/0.58    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f153,f129])).
% 1.54/0.58  fof(f153,plain,(
% 1.54/0.58    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(resolution,[],[f75,f51])).
% 1.54/0.58  fof(f648,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.54/0.58    inference(backward_demodulation,[],[f643,f647])).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (3827)------------------------------
% 1.54/0.58  % (3827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (3827)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (3827)Memory used [KB]: 2430
% 1.54/0.58  % (3827)Time elapsed: 0.110 s
% 1.54/0.58  % (3827)------------------------------
% 1.54/0.58  % (3827)------------------------------
% 1.54/0.58  % (3816)Success in time 0.218 s
%------------------------------------------------------------------------------
