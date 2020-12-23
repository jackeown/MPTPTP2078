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
% DateTime   : Thu Dec  3 13:14:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 (1090 expanded)
%              Number of leaves         :   12 ( 212 expanded)
%              Depth                    :   23
%              Number of atoms          :  301 (5814 expanded)
%              Number of equality atoms :  123 (1906 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f206,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f124,f204])).

fof(f204,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f184,f153])).

fof(f153,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f152,f131])).

fof(f131,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f113,f123])).

fof(f123,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f88,f114])).

fof(f114,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f89,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f83,f87])).

fof(f87,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f33,f80])).

fof(f80,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f37,f40])).

fof(f37,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f84,f87])).

fof(f84,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f34,f80])).

fof(f34,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f113,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f89,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f152,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f151,f126])).

fof(f126,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f89,f123])).

fof(f151,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f127,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f127,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f90,f123])).

fof(f90,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f82,f87])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f32,f80])).

fof(f32,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,(
    k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f182,f183])).

fof(f183,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f172,f166])).

fof(f166,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f76,f134])).

fof(f134,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f76,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f35,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f172,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f130,f47])).

fof(f130,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f111,f123])).

fof(f111,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f110,f88])).

fof(f110,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f109,f35])).

fof(f109,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f108,f89])).

fof(f108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f96,f31])).

fof(f96,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f90,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f182,plain,(
    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f133,f180])).

fof(f180,plain,(
    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f171,f164])).

fof(f164,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f75,f134])).

fof(f75,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f73,f31])).

fof(f73,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f171,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f130,f46])).

fof(f133,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f129,f123])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f103,f123])).

fof(f103,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f102,f101])).

fof(f101,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f99,f88])).

fof(f99,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f98,f89])).

fof(f98,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f93,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f102,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f92,f101])).

fof(f92,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f91,f87])).

fof(f91,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f85,f87])).

fof(f85,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f30,f80])).

fof(f30,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f78,f123])).

fof(f78,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:31:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (21216)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (21222)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (21222)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (21229)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f206,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(backward_demodulation,[],[f124,f204])).
% 0.22/0.48  fof(f204,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f202])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    k1_relat_1(sK2) != k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f184,f153])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.48    inference(forward_demodulation,[],[f152,f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f113,f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f88,f114])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(resolution,[],[f89,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.48    inference(backward_demodulation,[],[f83,f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f38,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    l1_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.48    inference(backward_demodulation,[],[f33,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.48    inference(resolution,[],[f37,f40])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    l1_struct_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f84,f87])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f34,f80])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(resolution,[],[f89,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f151,f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.48    inference(backward_demodulation,[],[f89,f123])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.48    inference(resolution,[],[f127,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f90,f123])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f82,f87])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f32,f80])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k1_relat_1(sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f182,f183])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f172,f166])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f76,f134])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f121,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 0.22/0.48    inference(resolution,[],[f89,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f35,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v2_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f130,f47])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.48    inference(backward_demodulation,[],[f111,f123])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f110,f88])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f109,f35])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f89])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f96,f31])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.48    inference(resolution,[],[f90,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f181])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    k2_relat_1(sK2) != k2_relat_1(sK2) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f133,f180])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f171,f164])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f75,f134])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f73,f31])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f35,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f130,f46])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f129,f123])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f103,f123])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f102,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f35])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f99,f88])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f98,f89])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f93,f31])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    inference(resolution,[],[f90,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f92,f101])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f91,f87])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f85,f87])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f81,f80])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f30,f80])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f78,f123])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f77,f37])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~l1_struct_0(sK1) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.48    inference(resolution,[],[f36,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~v2_struct_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (21222)------------------------------
% 0.22/0.48  % (21222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21222)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (21222)Memory used [KB]: 1663
% 0.22/0.48  % (21222)Time elapsed: 0.056 s
% 0.22/0.48  % (21222)------------------------------
% 0.22/0.48  % (21222)------------------------------
% 0.22/0.48  % (21208)Success in time 0.123 s
%------------------------------------------------------------------------------
