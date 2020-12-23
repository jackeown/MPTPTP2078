%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:09 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  166 (35878 expanded)
%              Number of leaves         :   23 (7197 expanded)
%              Depth                    :   30
%              Number of atoms          :  391 (185859 expanded)
%              Number of equality atoms :  130 (58769 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(subsumption_resolution,[],[f424,f293])).

fof(f293,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f268,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f268,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f182,f262])).

fof(f262,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f258,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f258,plain,(
    v1_xboole_0(k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f216,f218,f188,f257,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f257,plain,(
    ~ v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f171,f170,f256,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f256,plain,(
    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f253,f190])).

fof(f190,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f166,f177])).

fof(f177,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f113,f115,f176,f76])).

fof(f176,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f56,f143,f141,f140,f71])).

fof(f140,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f108,f138])).

fof(f138,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f107,f135])).

fof(f135,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f108,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f107,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f105,f100])).

fof(f100,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f62,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f62,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f105,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f59,f101])).

fof(f101,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f63,f64])).

fof(f63,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f104,f100])).

fof(f104,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f58,f101])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f109,f138])).

fof(f109,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f103,f100])).

fof(f103,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f57,f101])).

fof(f57,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f143,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f112,f138])).

fof(f112,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f61,f62,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f108,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f113,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f70,f108,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f166,plain,(
    k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f162,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f162,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f158,f144])).

fof(f144,plain,(
    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f131,f138])).

fof(f131,plain,(
    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f128,f123])).

fof(f123,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f60,f113,f56,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,(
    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f108,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f158,plain,(
    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f140,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f253,plain,(
    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f247,f249])).

fof(f249,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f248,f214])).

fof(f214,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f213,f181])).

fof(f181,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f122,f177])).

fof(f122,plain,(
    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f120,f121])).

fof(f121,plain,(
    sK2 = k7_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f113,f115,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f120,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f113,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f213,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f60,f56,f113,f94,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f248,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(superposition,[],[f174,f175])).

fof(f175,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f171,f170,f74])).

fof(f174,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(unit_resulting_resolution,[],[f171,f73])).

fof(f247,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f246,f244])).

fof(f244,plain,(
    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f60,f56,f183,f186,f182,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f186,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f146,f177])).

fof(f146,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f135,f138])).

fof(f183,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f141,f177])).

fof(f246,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f245,f191])).

fof(f191,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f167,f177])).

fof(f167,plain,(
    k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f162,f85])).

fof(f245,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f195,f244])).

fof(f195,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f187,f177])).

fof(f187,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f147,f177])).

fof(f147,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f142,f138])).

fof(f142,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f111,f138])).

% (20811)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f111,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f110,f100])).

fof(f110,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f106,f100])).

fof(f106,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f102,f101])).

fof(f102,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f55,f101])).

fof(f55,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f170,plain,(
    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f162,f88])).

fof(f171,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f70,f162,f66])).

fof(f188,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f162,f177])).

fof(f218,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f60,f56,f183,f186,f182,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f216,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f56,f60,f183,f182,f186,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f182,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f140,f177])).

fof(f424,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f423,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f423,plain,(
    ! [X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f418,f298])).

fof(f298,plain,(
    ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f297,f96])).

fof(f297,plain,(
    ! [X0] : ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f260,f262])).

fof(f260,plain,(
    ! [X0] : ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f143,f258,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f418,plain,(
    ! [X1] :
      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ) ),
    inference(superposition,[],[f86,f307])).

fof(f307,plain,(
    ! [X0] : k2_relat_1(sK2) = k2_relset_1(X0,k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f293,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1) ) ),
    inference(superposition,[],[f85,f96])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:00:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (20793)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (20805)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (20795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (20794)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (20817)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (20798)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (20792)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (20798)Refutation not found, incomplete strategy% (20798)------------------------------
% 0.21/0.52  % (20798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20792)Refutation not found, incomplete strategy% (20792)------------------------------
% 0.21/0.52  % (20792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20792)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20792)Memory used [KB]: 10618
% 0.21/0.52  % (20792)Time elapsed: 0.103 s
% 0.21/0.52  % (20792)------------------------------
% 0.21/0.52  % (20792)------------------------------
% 0.21/0.52  % (20815)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (20801)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (20818)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (20800)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (20813)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (20798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20798)Memory used [KB]: 10618
% 0.21/0.52  % (20798)Time elapsed: 0.104 s
% 0.21/0.52  % (20798)------------------------------
% 0.21/0.52  % (20798)------------------------------
% 0.21/0.52  % (20808)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (20814)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (20807)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (20799)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (20810)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (20796)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (20806)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (20806)Refutation not found, incomplete strategy% (20806)------------------------------
% 0.21/0.53  % (20806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20806)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20806)Memory used [KB]: 6396
% 0.21/0.53  % (20806)Time elapsed: 0.117 s
% 0.21/0.53  % (20806)------------------------------
% 0.21/0.53  % (20806)------------------------------
% 0.21/0.54  % (20816)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (20802)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.45/0.55  % (20809)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.45/0.55  % (20799)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % (20804)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f425,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(subsumption_resolution,[],[f424,f293])).
% 1.45/0.56  fof(f293,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.56    inference(forward_demodulation,[],[f268,f97])).
% 1.45/0.56  fof(f97,plain,(
% 1.45/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.45/0.56    inference(equality_resolution,[],[f81])).
% 1.45/0.56  fof(f81,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.45/0.56  fof(f268,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))),
% 1.45/0.56    inference(backward_demodulation,[],[f182,f262])).
% 1.45/0.56  fof(f262,plain,(
% 1.45/0.56    k1_xboole_0 = k1_relat_1(sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f258,f65])).
% 1.45/0.56  fof(f65,plain,(
% 1.45/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.45/0.56  fof(f258,plain,(
% 1.45/0.56    v1_xboole_0(k1_relat_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f216,f218,f188,f257,f71])).
% 1.45/0.56  fof(f71,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f38])).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.45/0.56    inference(flattening,[],[f37])).
% 1.45/0.56  fof(f37,plain,(
% 1.45/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,axiom,(
% 1.45/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.45/0.56  fof(f257,plain,(
% 1.45/0.56    ~v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f171,f170,f256,f76])).
% 1.45/0.56  fof(f76,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f44])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.56    inference(flattening,[],[f43])).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,axiom,(
% 1.45/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.45/0.56  fof(f256,plain,(
% 1.45/0.56    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(superposition,[],[f253,f190])).
% 1.45/0.56  fof(f190,plain,(
% 1.45/0.56    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f166,f177])).
% 1.45/0.56  fof(f177,plain,(
% 1.45/0.56    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f113,f115,f176,f76])).
% 1.45/0.56  fof(f176,plain,(
% 1.45/0.56    v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f56,f143,f141,f140,f71])).
% 1.45/0.56  fof(f140,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.45/0.56    inference(backward_demodulation,[],[f108,f138])).
% 1.45/0.56  fof(f138,plain,(
% 1.45/0.56    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f107,f135])).
% 1.45/0.56  fof(f135,plain,(
% 1.45/0.56    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f108,f85])).
% 1.45/0.56  fof(f85,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.45/0.56  fof(f107,plain,(
% 1.45/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f105,f100])).
% 1.45/0.56  fof(f100,plain,(
% 1.45/0.56    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f62,f64])).
% 1.45/0.56  fof(f64,plain,(
% 1.45/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f28])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f20])).
% 1.45/0.56  fof(f20,axiom,(
% 1.45/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.45/0.56  fof(f62,plain,(
% 1.45/0.56    l1_struct_0(sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f24])).
% 1.45/0.56  fof(f24,negated_conjecture,(
% 1.45/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.45/0.56    inference(negated_conjecture,[],[f23])).
% 1.45/0.56  fof(f23,conjecture,(
% 1.45/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 1.45/0.56  fof(f105,plain,(
% 1.45/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f59,f101])).
% 1.45/0.56  fof(f101,plain,(
% 1.45/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f63,f64])).
% 1.45/0.56  fof(f63,plain,(
% 1.45/0.56    l1_struct_0(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f59,plain,(
% 1.45/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f108,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.45/0.56    inference(backward_demodulation,[],[f104,f100])).
% 1.45/0.56  fof(f104,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.45/0.56    inference(backward_demodulation,[],[f58,f101])).
% 1.45/0.56  fof(f58,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f141,plain,(
% 1.45/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f109,f138])).
% 1.45/0.56  fof(f109,plain,(
% 1.45/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.45/0.56    inference(backward_demodulation,[],[f103,f100])).
% 1.45/0.56  fof(f103,plain,(
% 1.45/0.56    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.45/0.56    inference(backward_demodulation,[],[f57,f101])).
% 1.45/0.56  fof(f57,plain,(
% 1.45/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f143,plain,(
% 1.45/0.56    ~v1_xboole_0(k2_relat_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f112,f138])).
% 1.45/0.56  fof(f112,plain,(
% 1.45/0.56    ~v1_xboole_0(k2_struct_0(sK1))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f61,f62,f67])).
% 1.45/0.56  fof(f67,plain,(
% 1.45/0.56    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f32])).
% 1.45/0.56  fof(f32,plain,(
% 1.45/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f31])).
% 1.45/0.56  fof(f31,plain,(
% 1.45/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f21])).
% 1.45/0.56  fof(f21,axiom,(
% 1.45/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.45/0.56  fof(f61,plain,(
% 1.45/0.56    ~v2_struct_0(sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f56,plain,(
% 1.45/0.56    v1_funct_1(sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f115,plain,(
% 1.45/0.56    v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f108,f88])).
% 1.45/0.56  fof(f88,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f50])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.45/0.56    inference(pure_predicate_removal,[],[f10])).
% 1.45/0.56  fof(f10,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.45/0.56  fof(f113,plain,(
% 1.45/0.56    v1_relat_1(sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f70,f108,f66])).
% 1.45/0.56  fof(f66,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f30])).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.45/0.56  fof(f70,plain,(
% 1.45/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f5])).
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.45/0.56  fof(f166,plain,(
% 1.45/0.56    k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f162,f84])).
% 1.45/0.56  fof(f84,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f46])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f14])).
% 1.45/0.56  fof(f14,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.45/0.56  fof(f162,plain,(
% 1.45/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.45/0.56    inference(forward_demodulation,[],[f158,f144])).
% 1.45/0.56  fof(f144,plain,(
% 1.45/0.56    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f131,f138])).
% 1.45/0.56  fof(f131,plain,(
% 1.45/0.56    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.45/0.56    inference(forward_demodulation,[],[f128,f123])).
% 1.45/0.56  fof(f123,plain,(
% 1.45/0.56    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f60,f113,f56,f68])).
% 1.45/0.56  fof(f68,plain,(
% 1.45/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = k4_relat_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f34])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(flattening,[],[f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.45/0.56  fof(f60,plain,(
% 1.45/0.56    v2_funct_1(sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f128,plain,(
% 1.45/0.56    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f108,f83])).
% 1.45/0.56  fof(f83,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f16])).
% 1.45/0.56  fof(f16,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 1.45/0.56  fof(f158,plain,(
% 1.45/0.56    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f140,f87])).
% 1.45/0.56  fof(f87,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f49])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 1.45/0.56  fof(f253,plain,(
% 1.45/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f250])).
% 1.45/0.56  fof(f250,plain,(
% 1.45/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f247,f249])).
% 1.45/0.56  fof(f249,plain,(
% 1.45/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f248,f214])).
% 1.45/0.56  fof(f214,plain,(
% 1.45/0.56    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f213,f181])).
% 1.45/0.56  fof(f181,plain,(
% 1.45/0.56    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f122,f177])).
% 1.45/0.56  fof(f122,plain,(
% 1.45/0.56    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2)),
% 1.45/0.56    inference(superposition,[],[f120,f121])).
% 1.45/0.56  fof(f121,plain,(
% 1.45/0.56    sK2 = k7_relat_1(sK2,k2_struct_0(sK0))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f113,f115,f74])).
% 1.45/0.56  fof(f74,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f42])).
% 1.45/0.56  fof(f42,plain,(
% 1.45/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.56    inference(flattening,[],[f41])).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.45/0.56  fof(f120,plain,(
% 1.45/0.56    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f113,f73])).
% 1.45/0.56  fof(f73,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f40])).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.45/0.56  fof(f213,plain,(
% 1.45/0.56    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f60,f56,f113,f94,f69])).
% 1.45/0.56  fof(f69,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(flattening,[],[f35])).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 1.45/0.56  fof(f94,plain,(
% 1.45/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.56    inference(equality_resolution,[],[f78])).
% 1.45/0.56  fof(f78,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.56  fof(f248,plain,(
% 1.45/0.56    k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.45/0.56    inference(superposition,[],[f174,f175])).
% 1.45/0.56  fof(f175,plain,(
% 1.45/0.56    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f171,f170,f74])).
% 1.45/0.56  fof(f174,plain,(
% 1.45/0.56    ( ! [X0] : (k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0)) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f171,f73])).
% 1.45/0.56  fof(f247,plain,(
% 1.45/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f246,f244])).
% 1.45/0.56  fof(f244,plain,(
% 1.45/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f60,f56,f183,f186,f182,f92])).
% 1.45/0.56  fof(f92,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f54])).
% 1.45/0.56  fof(f54,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.56    inference(flattening,[],[f53])).
% 1.45/0.56  fof(f53,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.45/0.56    inference(ennf_transformation,[],[f22])).
% 1.45/0.56  fof(f22,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.45/0.56  fof(f186,plain,(
% 1.45/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f146,f177])).
% 1.45/0.56  fof(f146,plain,(
% 1.45/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f135,f138])).
% 1.45/0.56  fof(f183,plain,(
% 1.45/0.56    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f141,f177])).
% 1.45/0.56  fof(f246,plain,(
% 1.45/0.56    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f245,f191])).
% 1.45/0.56  fof(f191,plain,(
% 1.45/0.56    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f167,f177])).
% 1.45/0.56  fof(f167,plain,(
% 1.45/0.56    k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f162,f85])).
% 1.45/0.56  fof(f245,plain,(
% 1.45/0.56    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f195,f244])).
% 1.45/0.56  fof(f195,plain,(
% 1.45/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f187,f177])).
% 1.45/0.56  fof(f187,plain,(
% 1.45/0.56    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f147,f177])).
% 1.45/0.56  fof(f147,plain,(
% 1.45/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f142,f138])).
% 1.45/0.56  fof(f142,plain,(
% 1.45/0.56    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f111,f138])).
% 1.45/0.56  % (20811)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.45/0.56  fof(f111,plain,(
% 1.45/0.56    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f110,f100])).
% 1.45/0.56  fof(f110,plain,(
% 1.45/0.56    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f106,f100])).
% 1.45/0.56  fof(f106,plain,(
% 1.45/0.56    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f102,f101])).
% 1.45/0.56  fof(f102,plain,(
% 1.45/0.56    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f55,f101])).
% 1.45/0.56  fof(f55,plain,(
% 1.45/0.56    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f170,plain,(
% 1.45/0.56    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f162,f88])).
% 1.45/0.56  fof(f171,plain,(
% 1.45/0.56    v1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f70,f162,f66])).
% 1.45/0.56  fof(f188,plain,(
% 1.45/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.45/0.56    inference(backward_demodulation,[],[f162,f177])).
% 1.45/0.56  fof(f218,plain,(
% 1.45/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f60,f56,f183,f186,f182,f90])).
% 1.45/0.56  fof(f90,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f52])).
% 1.45/0.56  fof(f52,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.56    inference(flattening,[],[f51])).
% 1.45/0.56  fof(f51,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.45/0.56    inference(ennf_transformation,[],[f19])).
% 1.45/0.56  fof(f19,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.45/0.56  fof(f216,plain,(
% 1.45/0.56    v1_funct_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f56,f60,f183,f182,f186,f89])).
% 1.45/0.56  fof(f89,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f52])).
% 1.45/0.56  fof(f182,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.45/0.56    inference(backward_demodulation,[],[f140,f177])).
% 1.45/0.56  fof(f424,plain,(
% 1.45/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.56    inference(forward_demodulation,[],[f423,f96])).
% 1.45/0.56  fof(f96,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.45/0.56    inference(equality_resolution,[],[f82])).
% 1.45/0.56  fof(f82,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f3])).
% 1.45/0.56  fof(f423,plain,(
% 1.45/0.56    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))) )),
% 1.45/0.56    inference(subsumption_resolution,[],[f418,f298])).
% 1.45/0.56  fof(f298,plain,(
% 1.45/0.56    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.56    inference(forward_demodulation,[],[f297,f96])).
% 1.45/0.56  fof(f297,plain,(
% 1.45/0.56    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.45/0.56    inference(forward_demodulation,[],[f260,f262])).
% 1.45/0.56  fof(f260,plain,(
% 1.45/0.56    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK2))))) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f143,f258,f72])).
% 1.45/0.56  fof(f72,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f39])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f11])).
% 1.45/0.56  fof(f11,axiom,(
% 1.45/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.45/0.56  fof(f418,plain,(
% 1.45/0.56    ( ! [X1] : (m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))) )),
% 1.45/0.56    inference(superposition,[],[f86,f307])).
% 1.45/0.56  fof(f307,plain,(
% 1.45/0.56    ( ! [X0] : (k2_relat_1(sK2) = k2_relset_1(X0,k1_xboole_0,sK2)) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f293,f136])).
% 1.45/0.56  fof(f136,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)) )),
% 1.45/0.56    inference(superposition,[],[f85,f96])).
% 1.45/0.56  fof(f86,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f48])).
% 1.45/0.56  fof(f48,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (20799)------------------------------
% 1.45/0.56  % (20799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (20799)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (20799)Memory used [KB]: 1918
% 1.45/0.56  % (20799)Time elapsed: 0.093 s
% 1.45/0.56  % (20799)------------------------------
% 1.45/0.56  % (20799)------------------------------
% 1.45/0.56  % (20791)Success in time 0.195 s
%------------------------------------------------------------------------------
