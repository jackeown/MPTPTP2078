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
% DateTime   : Thu Dec  3 13:14:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  157 (5424 expanded)
%              Number of leaves         :   14 (1056 expanded)
%              Depth                    :   29
%              Number of atoms          :  562 (26418 expanded)
%              Number of equality atoms :  126 (4593 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(subsumption_resolution,[],[f286,f266])).

fof(f266,plain,(
    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f106,f261])).

fof(f261,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f260,f159])).

fof(f159,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f155,f88])).

fof(f88,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f87,plain,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f86,f79])).

fof(f79,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f78,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f71,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f39,f68])).

fof(f68,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f86,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f155,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f153,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f153,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f152,f37])).

fof(f152,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f151,f41])).

fof(f151,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f76,f90])).

fof(f90,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f75,f89])).

fof(f89,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f60,f76])).

fof(f75,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f72,f69])).

fof(f72,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f40,f68])).

fof(f40,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f150,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f149,f92])).

fof(f92,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f77,f90])).

fof(f77,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f70,f69])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f38,f68])).

fof(f38,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f149,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(superposition,[],[f63,f91])).

fof(f91,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f89,f90])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f260,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f259,f186])).

fof(f186,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f185,f41])).

fof(f185,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f184,f37])).

fof(f184,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f183,f93])).

fof(f183,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f182,f92])).

fof(f182,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(superposition,[],[f64,f91])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f259,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f258,f41])).

fof(f258,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f257,f93])).

fof(f257,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f256,f92])).

fof(f256,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f255,f37])).

fof(f255,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(trivial_inequality_removal,[],[f254])).

fof(f254,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(superposition,[],[f251,f91])).

fof(f251,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
      | ~ v2_funct_1(X0)
      | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0)) ) ),
    inference(subsumption_resolution,[],[f249,f45])).

fof(f249,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
      | ~ l1_struct_0(sK0)
      | ~ v2_funct_1(X0)
      | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0)) ) ),
    inference(superposition,[],[f248,f69])).

fof(f248,plain,(
    ! [X2,X3] :
      ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2))))
      | ~ l1_struct_0(X2)
      | ~ v2_funct_1(X3)
      | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3)) ) ),
    inference(forward_demodulation,[],[f247,f90])).

fof(f247,plain,(
    ! [X2,X3] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2))))
      | ~ l1_struct_0(X2)
      | ~ v2_funct_1(X3)
      | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3)) ) ),
    inference(subsumption_resolution,[],[f246,f44])).

fof(f246,plain,(
    ! [X2,X3] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2))))
      | ~ l1_struct_0(X2)
      | ~ v2_funct_1(X3)
      | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3)) ) ),
    inference(subsumption_resolution,[],[f241,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f241,plain,(
    ! [X2,X3] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2))))
      | ~ l1_struct_0(X2)
      | ~ v2_funct_1(X3)
      | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3)) ) ),
    inference(superposition,[],[f50,f95])).

fof(f95,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f68,f90])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

% (17646)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f106,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f105,plain,
    ( ~ v1_funct_1(sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(subsumption_resolution,[],[f104,f92])).

fof(f104,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(resolution,[],[f67,f93])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

% (17644)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
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
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f286,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f272,f285])).

fof(f285,plain,(
    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f273])).

fof(f273,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f193,f261])).

fof(f193,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(inner_rewriting,[],[f192])).

fof(f192,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f191,f82])).

fof(f82,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f81,plain,
    ( ~ v2_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f80,f79])).

fof(f80,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f191,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f190,f161])).

fof(f161,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f160,f141])).

fof(f141,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f140,f47])).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f140,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f139,f103])).

fof(f103,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f101,f79])).

fof(f101,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f139,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f138,f79])).

fof(f138,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f137,f122])).

fof(f122,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f37])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f120,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f119,f93])).

fof(f119,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f118,f92])).

fof(f118,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f61,f91])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f137,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f135,f37])).

fof(f135,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f57,f88])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f160,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f156,f59])).

fof(f156,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f153,f51])).

fof(f190,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f189,f122])).

fof(f189,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f188,f153])).

fof(f188,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f181,f147])).

fof(f147,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f146,f37])).

fof(f146,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f145,f41])).

fof(f145,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f144,f93])).

fof(f144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f143,f92])).

fof(f143,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(superposition,[],[f62,f91])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f181,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(superposition,[],[f64,f159])).

fof(f272,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f187,f261])).

fof(f187,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f94,f186])).

fof(f94,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f74,f90])).

fof(f74,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f73,f69])).

% (17626)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f73,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f42,f68])).

fof(f42,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17635)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (17634)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (17625)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (17637)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (17640)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (17628)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (17641)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (17627)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (17640)Refutation not found, incomplete strategy% (17640)------------------------------
% 0.22/0.51  % (17640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17640)Memory used [KB]: 1663
% 0.22/0.51  % (17640)Time elapsed: 0.097 s
% 0.22/0.51  % (17640)------------------------------
% 0.22/0.51  % (17640)------------------------------
% 0.22/0.51  % (17634)Refutation not found, incomplete strategy% (17634)------------------------------
% 0.22/0.51  % (17634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17634)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17634)Memory used [KB]: 10618
% 0.22/0.51  % (17634)Time elapsed: 0.092 s
% 0.22/0.51  % (17634)------------------------------
% 0.22/0.51  % (17634)------------------------------
% 0.22/0.51  % (17638)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (17632)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (17636)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (17642)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (17645)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (17624)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (17627)Refutation not found, incomplete strategy% (17627)------------------------------
% 0.22/0.52  % (17627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17627)Memory used [KB]: 10618
% 0.22/0.52  % (17627)Time elapsed: 0.103 s
% 0.22/0.52  % (17627)------------------------------
% 0.22/0.52  % (17627)------------------------------
% 0.22/0.52  % (17637)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f286,f266])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f106,f261])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f260,f159])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f155,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f86,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f78,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f51,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.52    inference(backward_demodulation,[],[f71,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f48,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    l1_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.52    inference(backward_demodulation,[],[f39,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f48,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    l1_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f54,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f153,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f152,f37])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f151,f41])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f150,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.52    inference(backward_demodulation,[],[f76,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f75,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f60,f76])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f72,f69])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f40,f68])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f149,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f77,f90])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f70,f69])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f38,f68])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.52    inference(superposition,[],[f63,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f89,f90])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f259,f186])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f185,f41])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f184,f37])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f183,f93])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f182,f92])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.52    inference(superposition,[],[f64,f91])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f258,f41])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f257,f93])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f256,f92])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f255,f37])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f254])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    inference(superposition,[],[f251,f91])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(X0) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f249,f45])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~l1_struct_0(sK0) | ~v2_funct_1(X0) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0))) )),
% 0.22/0.52    inference(superposition,[],[f248,f69])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k2_relat_1(sK2) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2)))) | ~l1_struct_0(X2) | ~v2_funct_1(X3) | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f247,f90])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2)))) | ~l1_struct_0(X2) | ~v2_funct_1(X3) | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f246,f44])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3) | ~l1_struct_0(sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2)))) | ~l1_struct_0(X2) | ~v2_funct_1(X3) | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f241,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X2),k2_relat_1(sK2),X3) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_relat_1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_relat_1(sK2)))) | ~l1_struct_0(X2) | ~v2_funct_1(X3) | k2_struct_0(X2) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),k2_relat_1(sK2),X3))) )),
% 0.22/0.52    inference(superposition,[],[f50,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f68,f90])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  % (17646)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f105,f37])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f92])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.52    inference(resolution,[],[f67,f93])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.52  % (17644)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.22/0.52    inference(condensation,[],[f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f272,f285])).
% 0.22/0.52  fof(f285,plain,(
% 0.22/0.52    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f273])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    k1_relat_1(sK2) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f193,f261])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.52    inference(inner_rewriting,[],[f192])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f191,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f81,f41])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f80,f79])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f52,f37])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f160,f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f139,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f102,f41])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f101,f79])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f56,f37])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f138,f79])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f137,f122])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f121,f37])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f120,f41])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f119,f93])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f92])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(superposition,[],[f61,f91])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f37])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(equality_resolution,[],[f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK2))) )),
% 0.22/0.52    inference(superposition,[],[f57,f88])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f156,f59])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))) | v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.53    inference(resolution,[],[f153,f51])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    k2_struct_0(sK0) != k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f189,f122])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f188,f153])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f181,f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f146,f37])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f145,f41])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f144,f93])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f143,f92])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f142])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.53    inference(superposition,[],[f62,f91])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.53    inference(superposition,[],[f64,f159])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f187,f261])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f94,f186])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f74,f90])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f73,f69])).
% 0.22/0.53  % (17626)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f42,f68])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (17637)------------------------------
% 0.22/0.53  % (17637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17643)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (17637)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (17637)Memory used [KB]: 6396
% 0.22/0.53  % (17637)Time elapsed: 0.106 s
% 0.22/0.53  % (17637)------------------------------
% 0.22/0.53  % (17637)------------------------------
% 0.22/0.53  % (17623)Success in time 0.162 s
%------------------------------------------------------------------------------
