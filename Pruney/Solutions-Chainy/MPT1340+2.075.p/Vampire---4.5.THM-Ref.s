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
% DateTime   : Thu Dec  3 13:14:29 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  119 (10020 expanded)
%              Number of leaves         :   15 (2000 expanded)
%              Depth                    :   24
%              Number of atoms          :  384 (48157 expanded)
%              Number of equality atoms :   71 (7963 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(subsumption_resolution,[],[f188,f116])).

fof(f116,plain,(
    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f106,f107])).

fof(f107,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f88,f89,f105,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f105,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f42,f96,f97,f98,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f81,f94])).

fof(f94,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f80,f93])).

fof(f93,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f80,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f77,f73])).

fof(f73,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f49,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f77,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f45,f74])).

fof(f74,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f50,f51])).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f76,f73])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f44,f74])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f82,f94])).

fof(f82,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f43,f74])).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f86,f94])).

fof(f86,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f83,f73])).

fof(f83,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f49,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f88,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f58,f81,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f106,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f42,f97,f98,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f188,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f136,f185])).

fof(f185,plain,(
    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f183,f90])).

fof(f90,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f88,f42,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,(
    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f125,f126,f134,f127,f169,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f169,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f166,f135])).

fof(f135,plain,(
    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f46,f42,f112,f111,f113,f67])).

fof(f113,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f98,f107])).

fof(f111,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f95,f107])).

fof(f95,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f93,f94])).

fof(f112,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f97,f107])).

fof(f166,plain,(
    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(unit_resulting_resolution,[],[f42,f46,f112,f113,f111,f163])).

fof(f163,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0)) ) ),
    inference(forward_demodulation,[],[f162,f94])).

fof(f162,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0)) ) ),
    inference(subsumption_resolution,[],[f160,f49])).

fof(f160,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0)) ) ),
    inference(superposition,[],[f144,f100])).

fof(f100,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f73,f94])).

fof(f144,plain,(
    ! [X2,X3] :
      ( k2_struct_0(X2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X2),X3)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
      | ~ v2_funct_1(X3)
      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X2),X3)) ) ),
    inference(subsumption_resolution,[],[f140,f50])).

fof(f140,plain,(
    ! [X2,X3] :
      ( k2_struct_0(X2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X2),X3)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
      | ~ l1_struct_0(sK0)
      | ~ v2_funct_1(X3)
      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X2),X3)) ) ),
    inference(superposition,[],[f52,f108])).

fof(f108,plain,(
    u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f74,f107])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f127,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f42,f46,f112,f111,f113,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f134,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f130,f92])).

fof(f92,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f88,f42,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f130,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f127,f62])).

fof(f126,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f42,f112,f111,f113,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f125,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f42,f46,f112,f111,f113,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f136,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f114,f135])).

fof(f114,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f99,f107])).

fof(f99,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f79,f94])).

fof(f79,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f78,f73])).

fof(f78,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f47,f74])).

fof(f47,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (804388864)
% 0.14/0.37  ipcrm: permission denied for id (804421635)
% 0.14/0.37  ipcrm: permission denied for id (804454404)
% 0.14/0.37  ipcrm: permission denied for id (804585480)
% 0.14/0.38  ipcrm: permission denied for id (804618249)
% 0.14/0.38  ipcrm: permission denied for id (804683787)
% 0.14/0.38  ipcrm: permission denied for id (804749326)
% 0.14/0.38  ipcrm: permission denied for id (804782095)
% 0.14/0.38  ipcrm: permission denied for id (804814864)
% 0.14/0.39  ipcrm: permission denied for id (804847633)
% 0.14/0.39  ipcrm: permission denied for id (804945940)
% 0.14/0.39  ipcrm: permission denied for id (805044247)
% 0.14/0.40  ipcrm: permission denied for id (805109788)
% 0.21/0.40  ipcrm: permission denied for id (805240863)
% 0.21/0.40  ipcrm: permission denied for id (805273632)
% 0.21/0.41  ipcrm: permission denied for id (805339170)
% 0.21/0.41  ipcrm: permission denied for id (805371939)
% 0.21/0.41  ipcrm: permission denied for id (805437477)
% 0.21/0.42  ipcrm: permission denied for id (805601322)
% 0.21/0.42  ipcrm: permission denied for id (805666861)
% 0.21/0.42  ipcrm: permission denied for id (805732400)
% 0.21/0.43  ipcrm: permission denied for id (805797938)
% 0.21/0.43  ipcrm: permission denied for id (805830707)
% 0.21/0.43  ipcrm: permission denied for id (805896247)
% 0.21/0.44  ipcrm: permission denied for id (805994555)
% 0.21/0.44  ipcrm: permission denied for id (806027324)
% 0.21/0.44  ipcrm: permission denied for id (806060093)
% 0.21/0.44  ipcrm: permission denied for id (806191169)
% 0.21/0.45  ipcrm: permission denied for id (806223938)
% 0.21/0.45  ipcrm: permission denied for id (806289476)
% 0.21/0.46  ipcrm: permission denied for id (806453322)
% 0.21/0.46  ipcrm: permission denied for id (806486091)
% 0.21/0.47  ipcrm: permission denied for id (806912089)
% 0.21/0.48  ipcrm: permission denied for id (806944858)
% 0.21/0.48  ipcrm: permission denied for id (806977627)
% 0.21/0.48  ipcrm: permission denied for id (807010397)
% 0.21/0.48  ipcrm: permission denied for id (807043166)
% 0.21/0.48  ipcrm: permission denied for id (807174241)
% 0.21/0.49  ipcrm: permission denied for id (807141474)
% 0.21/0.49  ipcrm: permission denied for id (807207011)
% 0.21/0.49  ipcrm: permission denied for id (807239780)
% 0.21/0.49  ipcrm: permission denied for id (807272549)
% 0.21/0.49  ipcrm: permission denied for id (807305318)
% 0.21/0.49  ipcrm: permission denied for id (807370856)
% 0.21/0.49  ipcrm: permission denied for id (807403625)
% 0.21/0.50  ipcrm: permission denied for id (807469163)
% 0.21/0.50  ipcrm: permission denied for id (807501932)
% 0.21/0.50  ipcrm: permission denied for id (807534701)
% 0.21/0.51  ipcrm: permission denied for id (807796854)
% 0.21/0.51  ipcrm: permission denied for id (807829623)
% 0.21/0.52  ipcrm: permission denied for id (807927930)
% 0.21/0.52  ipcrm: permission denied for id (807993469)
% 0.21/0.52  ipcrm: permission denied for id (808059007)
% 0.99/0.66  % (1548)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.99/0.67  % (1553)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.99/0.67  % (1559)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.99/0.67  % (1561)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.99/0.68  % (1552)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.99/0.68  % (1544)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.99/0.68  % (1565)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.99/0.68  % (1558)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.99/0.69  % (1543)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.99/0.69  % (1548)Refutation found. Thanks to Tanya!
% 0.99/0.69  % SZS status Theorem for theBenchmark
% 0.99/0.69  % SZS output start Proof for theBenchmark
% 0.99/0.69  fof(f189,plain,(
% 0.99/0.69    $false),
% 0.99/0.69    inference(subsumption_resolution,[],[f188,f116])).
% 0.99/0.69  fof(f116,plain,(
% 0.99/0.69    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f106,f107])).
% 0.99/0.69  fof(f107,plain,(
% 0.99/0.69    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f88,f89,f105,f61])).
% 0.99/0.69  fof(f61,plain,(
% 0.99/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f33])).
% 0.99/0.69  fof(f33,plain,(
% 0.99/0.69    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.99/0.69    inference(flattening,[],[f32])).
% 0.99/0.69  fof(f32,plain,(
% 0.99/0.69    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.99/0.69    inference(ennf_transformation,[],[f8])).
% 0.99/0.69  fof(f8,axiom,(
% 0.99/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.99/0.69  fof(f105,plain,(
% 0.99/0.69    v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f42,f96,f97,f98,f59])).
% 0.99/0.69  fof(f59,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f31])).
% 0.99/0.69  fof(f31,plain,(
% 0.99/0.69    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.99/0.69    inference(flattening,[],[f30])).
% 0.99/0.69  fof(f30,plain,(
% 0.99/0.69    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.99/0.69    inference(ennf_transformation,[],[f7])).
% 0.99/0.69  fof(f7,axiom,(
% 0.99/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.99/0.69  fof(f98,plain,(
% 0.99/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.99/0.69    inference(backward_demodulation,[],[f81,f94])).
% 0.99/0.69  fof(f94,plain,(
% 0.99/0.69    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f80,f93])).
% 0.99/0.69  fof(f93,plain,(
% 0.99/0.69    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f81,f62])).
% 0.99/0.69  fof(f62,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f34])).
% 0.99/0.69  fof(f34,plain,(
% 0.99/0.69    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/0.69    inference(ennf_transformation,[],[f6])).
% 0.99/0.69  fof(f6,axiom,(
% 0.99/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.99/0.69  fof(f80,plain,(
% 0.99/0.69    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f77,f73])).
% 0.99/0.69  fof(f73,plain,(
% 0.99/0.69    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f49,f51])).
% 0.99/0.69  fof(f51,plain,(
% 0.99/0.69    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f20])).
% 0.99/0.69  fof(f20,plain,(
% 0.99/0.69    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.99/0.69    inference(ennf_transformation,[],[f11])).
% 0.99/0.69  fof(f11,axiom,(
% 0.99/0.69    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.99/0.69  fof(f49,plain,(
% 0.99/0.69    l1_struct_0(sK1)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f19,plain,(
% 0.99/0.69    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.99/0.69    inference(flattening,[],[f18])).
% 0.99/0.69  fof(f18,plain,(
% 0.99/0.69    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.99/0.69    inference(ennf_transformation,[],[f16])).
% 0.99/0.69  fof(f16,negated_conjecture,(
% 0.99/0.69    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.99/0.69    inference(negated_conjecture,[],[f15])).
% 0.99/0.69  fof(f15,conjecture,(
% 0.99/0.69    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.99/0.69  fof(f77,plain,(
% 0.99/0.69    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f45,f74])).
% 0.99/0.69  fof(f74,plain,(
% 0.99/0.69    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f50,f51])).
% 0.99/0.69  fof(f50,plain,(
% 0.99/0.69    l1_struct_0(sK0)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f45,plain,(
% 0.99/0.69    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f81,plain,(
% 0.99/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.99/0.69    inference(backward_demodulation,[],[f76,f73])).
% 0.99/0.69  fof(f76,plain,(
% 0.99/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.99/0.69    inference(backward_demodulation,[],[f44,f74])).
% 0.99/0.69  fof(f44,plain,(
% 0.99/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f97,plain,(
% 0.99/0.69    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.99/0.69    inference(backward_demodulation,[],[f82,f94])).
% 0.99/0.69  fof(f82,plain,(
% 0.99/0.69    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.99/0.69    inference(backward_demodulation,[],[f75,f73])).
% 0.99/0.69  fof(f75,plain,(
% 0.99/0.69    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.99/0.69    inference(backward_demodulation,[],[f43,f74])).
% 0.99/0.69  fof(f43,plain,(
% 0.99/0.69    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f96,plain,(
% 0.99/0.69    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.99/0.69    inference(backward_demodulation,[],[f86,f94])).
% 0.99/0.69  fof(f86,plain,(
% 0.99/0.69    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.99/0.69    inference(forward_demodulation,[],[f83,f73])).
% 0.99/0.69  fof(f83,plain,(
% 0.99/0.69    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f48,f49,f54])).
% 0.99/0.69  fof(f54,plain,(
% 0.99/0.69    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f25])).
% 0.99/0.69  fof(f25,plain,(
% 0.99/0.69    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.99/0.69    inference(flattening,[],[f24])).
% 0.99/0.69  fof(f24,plain,(
% 0.99/0.69    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.99/0.69    inference(ennf_transformation,[],[f12])).
% 0.99/0.69  fof(f12,axiom,(
% 0.99/0.69    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.99/0.69  fof(f48,plain,(
% 0.99/0.69    ~v2_struct_0(sK1)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f42,plain,(
% 0.99/0.69    v1_funct_1(sK2)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f89,plain,(
% 0.99/0.69    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f81,f63])).
% 0.99/0.69  fof(f63,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f35])).
% 0.99/0.69  fof(f35,plain,(
% 0.99/0.69    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/0.69    inference(ennf_transformation,[],[f17])).
% 0.99/0.69  fof(f17,plain,(
% 0.99/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.99/0.69    inference(pure_predicate_removal,[],[f5])).
% 0.99/0.69  fof(f5,axiom,(
% 0.99/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.99/0.69  fof(f88,plain,(
% 0.99/0.69    v1_relat_1(sK2)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f58,f81,f53])).
% 0.99/0.69  fof(f53,plain,(
% 0.99/0.69    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f23])).
% 0.99/0.69  fof(f23,plain,(
% 0.99/0.69    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.99/0.69    inference(ennf_transformation,[],[f1])).
% 0.99/0.69  fof(f1,axiom,(
% 0.99/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.99/0.69  fof(f58,plain,(
% 0.99/0.69    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.99/0.69    inference(cnf_transformation,[],[f2])).
% 0.99/0.69  fof(f2,axiom,(
% 0.99/0.69    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.99/0.69  fof(f106,plain,(
% 0.99/0.69    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f42,f97,f98,f72])).
% 0.99/0.69  fof(f72,plain,(
% 0.99/0.69    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.99/0.69    inference(duplicate_literal_removal,[],[f71])).
% 0.99/0.69  fof(f71,plain,(
% 0.99/0.69    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.99/0.69    inference(equality_resolution,[],[f68])).
% 0.99/0.69  fof(f68,plain,(
% 0.99/0.69    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f41])).
% 0.99/0.69  fof(f41,plain,(
% 0.99/0.69    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.99/0.69    inference(flattening,[],[f40])).
% 0.99/0.69  fof(f40,plain,(
% 0.99/0.69    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.99/0.69    inference(ennf_transformation,[],[f9])).
% 0.99/0.69  fof(f9,axiom,(
% 0.99/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.99/0.69  fof(f188,plain,(
% 0.99/0.69    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f136,f185])).
% 0.99/0.69  fof(f185,plain,(
% 0.99/0.69    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.99/0.69    inference(forward_demodulation,[],[f183,f90])).
% 0.99/0.69  fof(f90,plain,(
% 0.99/0.69    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f46,f88,f42,f55])).
% 0.99/0.69  fof(f55,plain,(
% 0.99/0.69    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.99/0.69    inference(cnf_transformation,[],[f27])).
% 0.99/0.69  fof(f27,plain,(
% 0.99/0.69    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.99/0.69    inference(flattening,[],[f26])).
% 0.99/0.69  fof(f26,plain,(
% 0.99/0.69    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.99/0.69    inference(ennf_transformation,[],[f4])).
% 0.99/0.69  fof(f4,axiom,(
% 0.99/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.99/0.69  fof(f46,plain,(
% 0.99/0.69    v2_funct_1(sK2)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  fof(f183,plain,(
% 0.99/0.69    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f125,f126,f134,f127,f169,f67])).
% 0.99/0.69  fof(f67,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f39])).
% 0.99/0.69  fof(f39,plain,(
% 0.99/0.69    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.99/0.69    inference(flattening,[],[f38])).
% 0.99/0.69  fof(f38,plain,(
% 0.99/0.69    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.99/0.69    inference(ennf_transformation,[],[f13])).
% 0.99/0.69  fof(f13,axiom,(
% 0.99/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.99/0.69  fof(f169,plain,(
% 0.99/0.69    v2_funct_1(k2_funct_1(sK2))),
% 0.99/0.69    inference(forward_demodulation,[],[f166,f135])).
% 0.99/0.69  fof(f135,plain,(
% 0.99/0.69    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f46,f42,f112,f111,f113,f67])).
% 0.99/0.69  fof(f113,plain,(
% 0.99/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.99/0.69    inference(backward_demodulation,[],[f98,f107])).
% 0.99/0.69  fof(f111,plain,(
% 0.99/0.69    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f95,f107])).
% 0.99/0.69  fof(f95,plain,(
% 0.99/0.69    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f93,f94])).
% 0.99/0.69  fof(f112,plain,(
% 0.99/0.69    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.99/0.69    inference(backward_demodulation,[],[f97,f107])).
% 0.99/0.69  fof(f166,plain,(
% 0.99/0.69    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f42,f46,f112,f113,f111,f163])).
% 0.99/0.69  fof(f163,plain,(
% 0.99/0.69    ( ! [X0] : (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(X0) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0))) )),
% 0.99/0.69    inference(forward_demodulation,[],[f162,f94])).
% 0.99/0.69  fof(f162,plain,(
% 0.99/0.69    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(X0) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0))) )),
% 0.99/0.69    inference(subsumption_resolution,[],[f160,f49])).
% 0.99/0.69  fof(f160,plain,(
% 0.99/0.69    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0) | ~l1_struct_0(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(X0) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0))) )),
% 0.99/0.69    inference(superposition,[],[f144,f100])).
% 0.99/0.69  fof(f100,plain,(
% 0.99/0.69    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f73,f94])).
% 0.99/0.69  fof(f144,plain,(
% 0.99/0.69    ( ! [X2,X3] : (k2_struct_0(X2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X2),X3) | ~l1_struct_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_funct_1(X3) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X2),X3))) )),
% 0.99/0.69    inference(subsumption_resolution,[],[f140,f50])).
% 0.99/0.69  fof(f140,plain,(
% 0.99/0.69    ( ! [X2,X3] : (k2_struct_0(X2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X2),X3) | ~l1_struct_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~l1_struct_0(sK0) | ~v2_funct_1(X3) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X2),X3))) )),
% 0.99/0.69    inference(superposition,[],[f52,f108])).
% 0.99/0.69  fof(f108,plain,(
% 0.99/0.69    u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f74,f107])).
% 0.99/0.69  fof(f52,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.99/0.69    inference(cnf_transformation,[],[f22])).
% 0.99/0.69  fof(f22,plain,(
% 0.99/0.69    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.99/0.69    inference(flattening,[],[f21])).
% 0.99/0.69  fof(f21,plain,(
% 0.99/0.69    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.99/0.69    inference(ennf_transformation,[],[f14])).
% 0.99/0.69  fof(f14,axiom,(
% 0.99/0.69    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.99/0.69  fof(f127,plain,(
% 0.99/0.69    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f42,f46,f112,f111,f113,f66])).
% 0.99/0.69  fof(f66,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f37])).
% 0.99/0.69  fof(f37,plain,(
% 0.99/0.69    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.99/0.69    inference(flattening,[],[f36])).
% 0.99/0.69  fof(f36,plain,(
% 0.99/0.69    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.99/0.69    inference(ennf_transformation,[],[f10])).
% 0.99/0.69  fof(f10,axiom,(
% 0.99/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.99/0.69  fof(f134,plain,(
% 0.99/0.69    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.99/0.69    inference(forward_demodulation,[],[f130,f92])).
% 0.99/0.69  fof(f92,plain,(
% 0.99/0.69    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f46,f88,f42,f57])).
% 0.99/0.69  fof(f57,plain,(
% 0.99/0.69    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.99/0.69    inference(cnf_transformation,[],[f29])).
% 0.99/0.69  fof(f29,plain,(
% 0.99/0.69    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.99/0.69    inference(flattening,[],[f28])).
% 0.99/0.69  fof(f28,plain,(
% 0.99/0.69    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.99/0.69    inference(ennf_transformation,[],[f3])).
% 0.99/0.69  fof(f3,axiom,(
% 0.99/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.99/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.99/0.69  fof(f130,plain,(
% 0.99/0.69    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f127,f62])).
% 0.99/0.69  fof(f126,plain,(
% 0.99/0.69    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f46,f42,f112,f111,f113,f65])).
% 0.99/0.69  fof(f65,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.99/0.69    inference(cnf_transformation,[],[f37])).
% 0.99/0.69  fof(f125,plain,(
% 0.99/0.69    v1_funct_1(k2_funct_1(sK2))),
% 0.99/0.69    inference(unit_resulting_resolution,[],[f42,f46,f112,f111,f113,f64])).
% 0.99/0.69  fof(f64,plain,(
% 0.99/0.69    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 0.99/0.69    inference(cnf_transformation,[],[f37])).
% 0.99/0.69  fof(f136,plain,(
% 0.99/0.69    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f114,f135])).
% 0.99/0.69  fof(f114,plain,(
% 0.99/0.69    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f99,f107])).
% 0.99/0.69  fof(f99,plain,(
% 0.99/0.69    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f79,f94])).
% 0.99/0.69  fof(f79,plain,(
% 0.99/0.69    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f78,f73])).
% 0.99/0.69  fof(f78,plain,(
% 0.99/0.69    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.99/0.69    inference(backward_demodulation,[],[f47,f74])).
% 0.99/0.69  fof(f47,plain,(
% 0.99/0.69    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.99/0.69    inference(cnf_transformation,[],[f19])).
% 0.99/0.69  % SZS output end Proof for theBenchmark
% 0.99/0.69  % (1548)------------------------------
% 0.99/0.69  % (1548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.99/0.69  % (1548)Termination reason: Refutation
% 0.99/0.69  
% 0.99/0.69  % (1548)Memory used [KB]: 1791
% 0.99/0.69  % (1548)Time elapsed: 0.108 s
% 0.99/0.69  % (1548)------------------------------
% 0.99/0.69  % (1548)------------------------------
% 0.99/0.69  % (1402)Success in time 0.331 s
%------------------------------------------------------------------------------
