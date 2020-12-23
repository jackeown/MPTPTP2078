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
% DateTime   : Thu Dec  3 13:13:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 (1072 expanded)
%              Number of leaves         :   17 ( 218 expanded)
%              Depth                    :   20
%              Number of atoms          :  253 (4423 expanded)
%              Number of equality atoms :   98 (1655 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f295,f284])).

fof(f284,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f74])).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f258,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f198,f221])).

fof(f221,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f153,f210])).

fof(f210,plain,(
    k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f130,f208])).

fof(f208,plain,(
    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(superposition,[],[f157,f127])).

fof(f127,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f124,f84])).

fof(f84,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f82])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f79,f77])).

fof(f77,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f39,f76])).

fof(f76,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1))) ),
    inference(resolution,[],[f114,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f114,plain,(
    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f113,f84])).

fof(f113,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f92,plain,(
    v5_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(resolution,[],[f62,f82])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f157,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f154,f47])).

fof(f154,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f104,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(sK2,X3)) = k10_relat_1(sK2,k1_relat_1(X3)) ) ),
    inference(resolution,[],[f50,f84])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f130,plain,(
    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(superposition,[],[f81,f105])).

fof(f105,plain,(
    ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f66,f82])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f81,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f80,f77])).

fof(f80,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f40,f76])).

fof(f40,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f153,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f152,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f151,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))
    | k1_xboole_0 = sK2
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f129,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f122,f84])).

fof(f122,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f121,f89])).

fof(f89,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f61,f82])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f121,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f112,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f112,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f111,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f108,f83])).

fof(f83,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f78,f77])).

fof(f78,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f38,f76])).

fof(f38,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f63,f82])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f129,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f95,f82])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f198,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(equality_factoring,[],[f149])).

fof(f149,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f36,f123])).

fof(f36,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f295,plain,(
    k1_xboole_0 != k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f261,f74])).

fof(f261,plain,(
    k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f210,f221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (4405)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.46  % (4397)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (4401)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (4405)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f296,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f295,f284])).
% 0.22/0.47  fof(f284,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f258,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.47    inference(superposition,[],[f47,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f258,plain,(
% 0.22/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    inference(backward_demodulation,[],[f198,f221])).
% 0.22/0.47  fof(f221,plain,(
% 0.22/0.47    k1_xboole_0 = sK2),
% 0.22/0.47    inference(subsumption_resolution,[],[f153,f210])).
% 0.22/0.47  fof(f210,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k1_relat_1(sK2)),
% 0.22/0.47    inference(backward_demodulation,[],[f130,f208])).
% 0.22/0.47  fof(f208,plain,(
% 0.22/0.47    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)),
% 0.22/0.47    inference(superposition,[],[f157,f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f124,f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    v1_relat_1(sK2)),
% 0.22/0.47    inference(resolution,[],[f60,f82])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.47    inference(backward_demodulation,[],[f79,f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.47    inference(resolution,[],[f49,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    l1_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f17])).
% 0.22/0.47  fof(f17,conjecture,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,axiom,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.47    inference(backward_demodulation,[],[f39,f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.47    inference(resolution,[],[f49,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    l1_struct_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    ~v1_relat_1(sK2) | sK2 = k5_relat_1(sK2,k6_relat_1(k2_struct_0(sK1)))),
% 0.22/0.47    inference(resolution,[],[f114,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.22/0.47    inference(subsumption_resolution,[],[f113,f84])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~v1_relat_1(sK2)),
% 0.22/0.47    inference(resolution,[],[f92,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    v5_relat_1(sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(resolution,[],[f62,f82])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f154,f47])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))) )),
% 0.22/0.47    inference(resolution,[],[f104,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ( ! [X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(sK2,X3)) = k10_relat_1(sK2,k1_relat_1(X3))) )),
% 0.22/0.47    inference(resolution,[],[f50,f84])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(superposition,[],[f81,f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.22/0.47    inference(resolution,[],[f66,f82])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(backward_demodulation,[],[f80,f77])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(backward_demodulation,[],[f40,f76])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.22/0.47    inference(subsumption_resolution,[],[f152,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.47    inference(forward_demodulation,[],[f151,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    ~v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) | k1_xboole_0 = sK2 | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.47    inference(superposition,[],[f129,f123])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f122,f84])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f121,f89])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f61,f82])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f31])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK1) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.47    inference(resolution,[],[f112,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    v1_partfun1(sK2,k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f111,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    v1_funct_1(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f108,f83])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.47    inference(backward_demodulation,[],[f78,f77])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.47    inference(backward_demodulation,[],[f38,f76])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f63,f82])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.47    inference(flattening,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ~v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | k1_xboole_0 = sK2),
% 0.22/0.47    inference(resolution,[],[f95,f82])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(resolution,[],[f65,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.47    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.47  fof(f198,plain,(
% 0.22/0.47    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    inference(equality_factoring,[],[f149])).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f140])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_struct_0(sK0) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.47    inference(superposition,[],[f36,f123])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f295,plain,(
% 0.22/0.47    k1_xboole_0 != k2_struct_0(sK0)),
% 0.22/0.47    inference(forward_demodulation,[],[f261,f74])).
% 0.22/0.47  fof(f261,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k1_relat_1(k1_xboole_0)),
% 0.22/0.47    inference(backward_demodulation,[],[f210,f221])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (4405)------------------------------
% 0.22/0.47  % (4405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4405)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (4405)Memory used [KB]: 1791
% 0.22/0.47  % (4405)Time elapsed: 0.067 s
% 0.22/0.47  % (4405)------------------------------
% 0.22/0.47  % (4405)------------------------------
% 0.22/0.47  % (4387)Success in time 0.109 s
%------------------------------------------------------------------------------
