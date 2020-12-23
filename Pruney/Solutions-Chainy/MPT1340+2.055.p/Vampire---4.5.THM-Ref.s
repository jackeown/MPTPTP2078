%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  211 (9492 expanded)
%              Number of leaves         :   20 (1865 expanded)
%              Depth                    :   62
%              Number of atoms          :  699 (45605 expanded)
%              Number of equality atoms :  210 (7381 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(subsumption_resolution,[],[f393,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f393,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f143,f390])).

fof(f390,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f389,f73])).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f389,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f388,f192])).

fof(f192,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f145,f186])).

fof(f186,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f185,f73])).

fof(f185,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) ),
    inference(resolution,[],[f138,f145])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k2_struct_0(sK0) = k1_relat_1(sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f137,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f137,plain,
    ( ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f108])).

fof(f108,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f105,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f105,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f104,f95])).

fof(f95,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f58,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f104,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f52,f94])).

fof(f94,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f57,f63])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f136,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f118,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f118,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f117,f102])).

fof(f102,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f101,f95])).

fof(f101,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f51,f94])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f117,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f106,f98])).

fof(f98,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f96,f57])).

fof(f96,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f65,f94])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f106,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f105,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f145,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f105,f141])).

fof(f141,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f140,f107])).

fof(f107,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f105,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f140,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f139,f95])).

fof(f139,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f53,f94])).

fof(f53,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f388,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k1_xboole_0 = k2_relat_1(sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f386,f64])).

fof(f386,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f383,f50])).

fof(f383,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f381,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f381,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f380,f194])).

fof(f194,plain,(
    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f148,f186])).

fof(f148,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f135,f141])).

fof(f135,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f115,f102])).

fof(f115,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(resolution,[],[f105,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f380,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f265,f379])).

fof(f379,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f359,f377])).

fof(f377,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f376,f73])).

fof(f376,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f375,f192])).

fof(f375,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k1_xboole_0 = k2_relat_1(sK2)
      | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f373,f64])).

fof(f373,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f371,f50])).

fof(f371,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f370,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f370,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f369,f73])).

fof(f369,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f350,f192])).

fof(f350,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k1_xboole_0 = k2_relat_1(sK2)
      | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f348,f64])).

fof(f348,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f345,f50])).

fof(f345,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f334,f67])).

fof(f334,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f332,f178])).

fof(f178,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f69,f176])).

fof(f176,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f175,f73])).

fof(f175,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) ),
    inference(resolution,[],[f103,f145])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | sK2 = k2_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f93,f64])).

fof(f93,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f92,f50])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f54,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f332,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f331,f73])).

fof(f331,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f325,f192])).

fof(f325,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k1_xboole_0 = k2_relat_1(sK2)
      | v2_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f323,f64])).

fof(f323,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f322,f54])).

fof(f322,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f321,f50])).

fof(f321,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f320])).

fof(f320,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f319,f69])).

fof(f319,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f318,f73])).

fof(f318,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f317,f192])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
      | k1_xboole_0 = k2_relat_1(sK2)
      | v2_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f315,f64])).

fof(f315,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f313,f50])).

fof(f313,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f312,f66])).

fof(f312,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f311,f73])).

fof(f311,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f288,f192])).

fof(f288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v2_funct_1(k2_funct_1(sK2))
      | k1_xboole_0 = k2_relat_1(sK2)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f286,f64])).

fof(f286,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f283,f50])).

fof(f283,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f281,f67])).

fof(f281,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f280,f180])).

fof(f180,plain,
    ( v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f66,f176])).

fof(f280,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f279,f50])).

fof(f279,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f278,f87])).

fof(f87,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f278,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f72,f276])).

fof(f276,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f275,f186])).

fof(f275,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f274,f141])).

fof(f274,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f273,f193])).

fof(f193,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f146,f186])).

fof(f146,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f107,f141])).

fof(f273,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f272,f186])).

fof(f272,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f130,f141])).

fof(f130,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f128,f50])).

fof(f128,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f113,f102])).

fof(f113,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f105,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
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
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f359,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f326,f332])).

fof(f326,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f254,f239])).

fof(f239,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f237,f77])).

fof(f237,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f236,f141])).

fof(f236,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f235,f186])).

fof(f235,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f234,f193])).

fof(f234,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f233,f186])).

fof(f233,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f124,f141])).

fof(f124,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f123,f54])).

fof(f123,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f122,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f111,f102])).

fof(f111,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f105,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f254,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f253,f176])).

fof(f253,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f244,f228])).

fof(f228,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f227,f141])).

fof(f227,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f226,f186])).

fof(f226,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f225,f193])).

fof(f225,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f224,f186])).

fof(f224,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f121,f141])).

fof(f121,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f120,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f119,f50])).

fof(f119,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f110,f102])).

fof(f110,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f105,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f244,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f237,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f265,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f232,f264])).

fof(f264,plain,(
    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f263,f186])).

fof(f263,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f262,f141])).

fof(f262,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f261,f193])).

fof(f261,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f260,f186])).

fof(f260,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f127,f141])).

fof(f127,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f112,f102])).

fof(f112,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f105,f83])).

fof(f232,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    inference(forward_demodulation,[],[f184,f186])).

fof(f184,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(forward_demodulation,[],[f183,f95])).

fof(f183,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(forward_demodulation,[],[f55,f142])).

fof(f142,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f94,f141])).

fof(f55,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f143,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f98,f141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (9197)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (9205)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (9198)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (9190)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (9205)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f409,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f393,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f393,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f143,f390])).
% 0.20/0.52  fof(f390,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f389,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f389,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f388,f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.52    inference(backward_demodulation,[],[f145,f186])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f185,f73])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f138,f145])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f137,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f136,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f105,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.52    inference(forward_demodulation,[],[f104,f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f58,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    l1_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f20])).
% 0.20/0.52  fof(f20,conjecture,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.52    inference(forward_demodulation,[],[f52,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.52    inference(resolution,[],[f57,f63])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    l1_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f118,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f117,f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.52    inference(forward_demodulation,[],[f101,f95])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.52    inference(forward_demodulation,[],[f51,f94])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f116,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f106,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f97,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f96,f57])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.20/0.52    inference(superposition,[],[f65,f94])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f105,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.52    inference(backward_demodulation,[],[f105,f141])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f140,f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f105,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f139,f95])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f53,f94])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f388,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f386,f64])).
% 0.20/0.52  fof(f386,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f383,f50])).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f381,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.52  fof(f381,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f380,f194])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f148,f186])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f135,f141])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f134,f50])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f115,f102])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.20/0.52    inference(resolution,[],[f105,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.20/0.52    inference(condensation,[],[f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.52  fof(f380,plain,(
% 0.20/0.52    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f265,f379])).
% 0.20/0.52  fof(f379,plain,(
% 0.20/0.52    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f359,f377])).
% 0.20/0.52  fof(f377,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f376,f73])).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f375,f192])).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f373,f64])).
% 0.20/0.52  fof(f373,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f371,f50])).
% 0.20/0.52  fof(f371,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f370,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f370,plain,(
% 0.20/0.52    ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f369,f73])).
% 0.20/0.52  fof(f369,plain,(
% 0.20/0.52    ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f350,f192])).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f348,f64])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f345,f50])).
% 0.20/0.52  fof(f345,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f334,f67])).
% 0.20/0.52  fof(f334,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f332,f178])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(superposition,[],[f69,f176])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f175,f73])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f103,f145])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f93,f64])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f92,f50])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f54,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    v2_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.52  fof(f332,plain,(
% 0.20/0.52    v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f331,f73])).
% 0.20/0.52  fof(f331,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f325,f192])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f323,f64])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f322,f54])).
% 0.20/0.52  fof(f322,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f321,f50])).
% 0.20/0.52  fof(f321,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f320])).
% 0.20/0.52  fof(f320,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f319,f69])).
% 0.20/0.52  fof(f319,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f318,f73])).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f317,f192])).
% 0.20/0.52  fof(f317,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f315,f64])).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f313,f50])).
% 0.20/0.52  fof(f313,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f312,f66])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f311,f73])).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.52    inference(resolution,[],[f288,f192])).
% 0.20/0.52  fof(f288,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(resolution,[],[f286,f64])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f283,f50])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f281,f67])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f280,f180])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(superposition,[],[f66,f176])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f279,f50])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f278,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f62,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f72,f276])).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f275,f186])).
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f274,f141])).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f273,f193])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f146,f186])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f107,f141])).
% 0.20/0.52  fof(f273,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f272,f186])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f130,f141])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f129,f54])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f128,f50])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f113,f102])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f105,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f326,f332])).
% 0.20/0.52  fof(f326,plain,(
% 0.20/0.52    ~v2_funct_1(k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f254,f239])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f237,f77])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.52    inference(forward_demodulation,[],[f236,f141])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))),
% 0.20/0.52    inference(forward_demodulation,[],[f235,f186])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(subsumption_resolution,[],[f234,f193])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(forward_demodulation,[],[f233,f186])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(forward_demodulation,[],[f124,f141])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(subsumption_resolution,[],[f123,f54])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(subsumption_resolution,[],[f122,f50])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(subsumption_resolution,[],[f111,f102])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.52    inference(resolution,[],[f105,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f253,f176])).
% 0.20/0.52  fof(f253,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f244,f228])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f227,f141])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f226,f186])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f225,f193])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f224,f186])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f121,f141])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f120,f54])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f119,f50])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f110,f102])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f105,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f237,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f232,f264])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f263,f186])).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f262,f141])).
% 0.20/0.52  fof(f262,plain,(
% 0.20/0.52    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f261,f193])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f260,f186])).
% 0.20/0.52  fof(f260,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f127,f141])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f126,f54])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f125,f50])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f112,f102])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    inference(resolution,[],[f105,f83])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f184,f186])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f183,f95])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f55,f142])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f94,f141])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f98,f141])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (9205)------------------------------
% 0.20/0.52  % (9205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9205)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (9205)Memory used [KB]: 1918
% 0.20/0.52  % (9205)Time elapsed: 0.112 s
% 0.20/0.52  % (9205)------------------------------
% 0.20/0.52  % (9205)------------------------------
% 0.20/0.53  % (9183)Success in time 0.167 s
%------------------------------------------------------------------------------
