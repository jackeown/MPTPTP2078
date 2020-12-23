%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (1839 expanded)
%              Number of leaves         :   14 ( 363 expanded)
%              Depth                    :   21
%              Number of atoms          :  326 (9480 expanded)
%              Number of equality atoms :   93 (2969 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f190,f189])).

fof(f189,plain,(
    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f147,f187])).

fof(f187,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f179,f96])).

fof(f96,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f95,f83])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f73])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f69,f66])).

fof(f66,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f41,f65])).

fof(f65,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f95,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f94,f39])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f179,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f114,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f113,f93])).

fof(f93,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f92,f83])).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f91,f39])).

fof(f91,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f112,f96])).

fof(f112,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f108,f85])).

fof(f85,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f80,f83])).

fof(f80,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f108,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f84,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f81,f83])).

fof(f81,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f146,f137])).

fof(f137,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f83])).

fof(f136,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f86])).

fof(f86,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f62,f73])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f135,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f127,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f127,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f126,f102])).

fof(f102,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f74,f99])).

fof(f99,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f72,f98])).

fof(f98,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f61,f73])).

fof(f72,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f70,f66])).

fof(f70,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f42,f65])).

fof(f42,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f68,f66])).

fof(f68,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f40,f65])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f126,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f125,f39])).

fof(f125,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f124,f104])).

fof(f104,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f79,f99])).

fof(f79,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f77,f45])).

fof(f77,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f49,f65])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f124,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f57,f101])).

fof(f101,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f73,f99])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f146,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f134,f137])).

fof(f134,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f133,f132])).

fof(f132,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f131,f43])).

fof(f131,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f130,f106])).

fof(f106,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f98,f99])).

fof(f130,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f129,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f128,f102])).

fof(f128,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f63,f101])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
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
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f133,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f107,f132])).

fof(f107,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f103,f99])).

fof(f103,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f76,f99])).

fof(f76,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f75,f66])).

fof(f75,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f71,f66])).

fof(f71,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f67,f65])).

fof(f67,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f38,f65])).

fof(f38,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f190,plain,(
    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f180,f93])).

fof(f180,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (26232)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (26230)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (26245)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (26247)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (26246)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (26231)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (26228)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (26245)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f190,f189])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f187])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f179,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f82,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f48,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    inference(backward_demodulation,[],[f69,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f47,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f47,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f55,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f114,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.50    inference(forward_demodulation,[],[f113,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f92,f83])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f91,f39])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f54,f43])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 0.20/0.50    inference(forward_demodulation,[],[f112,f96])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f80,f83])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f52,f39])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.20/0.50    inference(resolution,[],[f84,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f81,f83])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f53,f39])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f146,f137])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f136,f83])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f135,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f62,f73])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f127,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f126,f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f74,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f72,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f61,f73])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f70,f66])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f42,f65])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f68,f66])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f40,f65])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f125,f39])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f124,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f79,f99])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f77,f45])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f49,f65])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f57,f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.50    inference(backward_demodulation,[],[f73,f99])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f134,f137])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f133,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f131,f43])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f130,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f98,f99])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f129,f39])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f128,f102])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(resolution,[],[f63,f101])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f107,f132])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f103,f99])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f76,f99])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f75,f66])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f71,f66])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f67,f65])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f38,f65])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f180,f93])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f114,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (26245)------------------------------
% 0.20/0.50  % (26245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26245)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (26245)Memory used [KB]: 1663
% 0.20/0.50  % (26245)Time elapsed: 0.082 s
% 0.20/0.50  % (26245)------------------------------
% 0.20/0.50  % (26245)------------------------------
% 0.20/0.50  % (26220)Success in time 0.138 s
%------------------------------------------------------------------------------
