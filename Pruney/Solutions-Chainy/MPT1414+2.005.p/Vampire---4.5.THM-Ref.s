%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 555 expanded)
%              Number of leaves         :   14 ( 104 expanded)
%              Depth                    :   32
%              Number of atoms          :  719 (3422 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f205,f101])).

fof(f101,plain,(
    ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f96,f100])).

fof(f100,plain,(
    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f45,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (6448)Refutation not found, incomplete strategy% (6448)------------------------------
% (6448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r3_binop_1(X0,X2,X3)
                     => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r3_binop_1(X0,X2,X3)
                   => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).

fof(f99,plain,
    ( ~ v3_relat_2(sK1)
    | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f98,f44])).

fof(f44,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v3_relat_2(sK1)
    | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f46,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v3_relat_2(sK1)
    | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(f96,plain,(
    ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f94,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f93,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f92,f45])).

fof(f92,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_eqrel_1)).

fof(f205,plain,(
    v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f204,f45])).

fof(f204,plain,
    ( ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f203,f109])).

fof(f109,plain,(
    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f108,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f107,f47])).

fof(f107,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f106,f44])).

fof(f106,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f105,f46])).

fof(f105,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_relat_2(sK1) ),
    inference(superposition,[],[f64,f100])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v8_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(f203,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f202,f48])).

fof(f202,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f201,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f201,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f200,f47])).

fof(f200,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f199,f44])).

fof(f199,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f198,f46])).

fof(f198,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(resolution,[],[f197,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0))
      | ~ v8_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ v3_relat_2(X0)
      | v1_xboole_0(k8_eqrel_1(X1,X0)) ) ),
    inference(resolution,[],[f65,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(f197,plain,(
    ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f196,f126])).

fof(f126,plain,(
    r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f125,f43])).

fof(f125,plain,
    ( r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f124,f41])).

fof(f41,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK3)
      | r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f123,f82])).

fof(f82,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f81,f48])).

fof(f81,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f80,f72])).

fof(f72,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f71,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f51,f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f80,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0)
      | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f123,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_binop_1(sK0,X0,sK3)
      | ~ r3_binop_1(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f122,f76])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f75,f48])).

fof(f75,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f74,f72])).

fof(f74,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | v1_funct_1(sK3) ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_binop_1(sK0,X0,sK3)
      | ~ r3_binop_1(sK0,X0,sK3) ) ),
    inference(resolution,[],[f54,f85])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f84,f48])).

fof(f84,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f83,f72])).

fof(f83,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,X0)
      | r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

fof(f196,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f195,f131])).

fof(f131,plain,(
    r2_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,
    ( r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f129,f41])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK3)
      | r2_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f128,f82])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | r2_binop_1(sK0,X0,sK3)
      | ~ r3_binop_1(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f127,f76])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | r2_binop_1(sK0,X0,sK3)
      | ~ r3_binop_1(sK0,X0,sK3) ) ),
    inference(resolution,[],[f55,f85])).

% (6461)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (6453)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (6446)Refutation not found, incomplete strategy% (6446)------------------------------
% (6446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6446)Termination reason: Refutation not found, incomplete strategy

% (6446)Memory used [KB]: 10618
% (6446)Time elapsed: 0.113 s
% (6446)------------------------------
% (6446)------------------------------
% (6454)Refutation not found, incomplete strategy% (6454)------------------------------
% (6454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6454)Termination reason: Refutation not found, incomplete strategy

% (6454)Memory used [KB]: 1791
% (6454)Time elapsed: 0.116 s
% (6454)------------------------------
% (6454)------------------------------
% (6458)Termination reason: Refutation not found, incomplete strategy

% (6458)Memory used [KB]: 6140
% (6458)Time elapsed: 0.113 s
% (6458)------------------------------
% (6458)------------------------------
% (6448)Termination reason: Refutation not found, incomplete strategy

% (6448)Memory used [KB]: 10490
% (6448)Time elapsed: 0.116 s
% (6448)------------------------------
% (6448)------------------------------
fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,X0)
      | r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f195,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f194,f40])).

fof(f194,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f193,f43])).

fof(f193,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f192,f46])).

fof(f192,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f191,f44])).

fof(f191,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f190,f45])).

fof(f190,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f189,f48])).

fof(f189,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f188,f85])).

fof(f188,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f187,f82])).

fof(f187,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f186,f76])).

fof(f186,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f181,f47])).

fof(f181,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ r2_binop_1(sK0,sK2,sK3)
    | ~ r1_binop_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f180,f42])).

fof(f42,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0))
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v8_relat_2(X0)
      | ~ m1_subset_1(X3,X1)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ r2_binop_1(X1,X3,X2)
      | ~ r1_binop_1(X1,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v8_relat_2(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0))
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ m1_subset_1(X3,X1)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ r2_binop_1(X1,X3,X2)
      | ~ v1_partfun1(X0,X1)
      | ~ v3_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X3,X1)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ r1_binop_1(X1,X3,X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f178,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ r1_binop_1(X0,X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r1_binop_1(X0,X2,X3)
                   => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ v8_relat_2(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0))
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ m1_subset_1(X3,X1)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ r2_binop_1(X1,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0))
      | ~ r1_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ v1_partfun1(X0,X1)
      | r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ v1_partfun1(X0,X1)
      | ~ v3_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X3,X1)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ r2_binop_1(X1,X3,X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f158,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ r2_binop_1(X0,X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r2_binop_1(X0,X2,X3)
                   => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).

fof(f158,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))
      | ~ v3_relat_2(X4)
      | ~ v8_relat_2(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_zfmisc_1(X5,X5),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X7,k8_eqrel_1(X5,X4))
      | ~ r1_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))
      | ~ v1_partfun1(X4,X5)
      | r3_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) ) ),
    inference(subsumption_resolution,[],[f157,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f157,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_partfun1(X4,X5)
      | ~ v3_relat_2(X4)
      | ~ v8_relat_2(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_zfmisc_1(X5,X5),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
      | v1_xboole_0(X5)
      | ~ v1_funct_2(k3_filter_1(X5,X4,X6),k2_zfmisc_1(k8_eqrel_1(X5,X4),k8_eqrel_1(X5,X4)),k8_eqrel_1(X5,X4))
      | ~ m1_subset_1(X7,k8_eqrel_1(X5,X4))
      | ~ r1_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))
      | ~ r2_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))
      | r3_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) ) ),
    inference(subsumption_resolution,[],[f149,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | v1_xboole_0(X0)
      | v1_funct_1(k3_filter_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_partfun1(X4,X5)
      | ~ v3_relat_2(X4)
      | ~ v8_relat_2(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_zfmisc_1(X5,X5),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
      | v1_xboole_0(X5)
      | ~ v1_funct_1(k3_filter_1(X5,X4,X6))
      | ~ v1_funct_2(k3_filter_1(X5,X4,X6),k2_zfmisc_1(k8_eqrel_1(X5,X4),k8_eqrel_1(X5,X4)),k8_eqrel_1(X5,X4))
      | ~ m1_subset_1(X7,k8_eqrel_1(X5,X4))
      | ~ r1_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))
      | ~ r2_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))
      | r3_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) ) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | r3_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:56:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (6443)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (6441)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (6438)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (6439)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (6444)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (6441)Refutation not found, incomplete strategy% (6441)------------------------------
% 0.21/0.50  % (6441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6441)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6441)Memory used [KB]: 10618
% 0.21/0.50  % (6441)Time elapsed: 0.100 s
% 0.21/0.50  % (6441)------------------------------
% 0.21/0.50  % (6441)------------------------------
% 0.21/0.51  % (6451)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (6449)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (6454)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (6457)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (6459)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (6458)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (6451)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (6446)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (6452)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (6458)Refutation not found, incomplete strategy% (6458)------------------------------
% 0.21/0.51  % (6458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6448)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (6440)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (6456)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (6450)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (6442)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (6460)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (6447)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (6455)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f205,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f96,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v3_relat_2(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  % (6448)Refutation not found, incomplete strategy% (6448)------------------------------
% 0.21/0.52  % (6448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  fof(f15,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f14])).
% 0.21/0.52  fof(f14,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~v3_relat_2(sK1) | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_partfun1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~v1_partfun1(sK1,sK0) | ~v3_relat_2(sK1) | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    v8_relat_2(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~v8_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v3_relat_2(sK1) | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f63,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v1_partfun1(X1,X0) | ~v3_relat_2(X1) | k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f44])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0) | ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f93,f46])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~v8_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0) | ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f92,f45])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~v3_relat_2(sK1) | ~v8_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0) | ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f59,f47])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0) | ~v1_xboole_0(k7_eqrel_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k7_eqrel_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_eqrel_1)).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f204,f45])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f203,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f45])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f47])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_relat_2(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f44])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v1_partfun1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_relat_2(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f46])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v8_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_relat_2(sK1)),
% 0.21/0.52    inference(superposition,[],[f64,f100])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v8_relat_2(X1) | ~v1_partfun1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_relat_2(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f202,f48])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f201,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f200,f47])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f199,f44])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ~v1_partfun1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f198,f46])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ~v8_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_relat_2(sK1) | v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f197,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k9_eqrel_1(X1,X0,X2),k8_eqrel_1(X1,X0)) | ~v8_relat_2(X0) | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1) | ~m1_subset_1(k8_eqrel_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~v3_relat_2(X0) | v1_xboole_0(k8_eqrel_1(X1,X0))) )),
% 0.21/0.52    inference(resolution,[],[f65,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m2_subset_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~v1_partfun1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f43])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    r1_binop_1(sK0,sK2,sK3) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f124,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    r3_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0] : (~r3_binop_1(sK0,X0,sK3) | r1_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f81,f48])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f71,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f51,f47])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | v1_xboole_0(sK0) | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.53    inference(resolution,[],[f61,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    m2_filter_1(sK3,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0) | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X0,sK0) | r1_binop_1(sK0,X0,sK3) | ~r3_binop_1(sK0,X0,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f48])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | v1_funct_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f72])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | v1_xboole_0(sK0) | v1_funct_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f60,f40])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0) | v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X0,sK0) | r1_binop_1(sK0,X0,sK3) | ~r3_binop_1(sK0,X0,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f54,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f48])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f72])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | v1_xboole_0(sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.53    inference(resolution,[],[f62,f40])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m1_subset_1(X1,X0) | r1_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f195,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    r2_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f43])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    r2_binop_1(sK0,sK2,sK3) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f129,f41])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X0] : (~r3_binop_1(sK0,X0,sK3) | r2_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f82])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X0,sK0) | r2_binop_1(sK0,X0,sK3) | ~r3_binop_1(sK0,X0,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f76])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X0,sK0) | r2_binop_1(sK0,X0,sK3) | ~r3_binop_1(sK0,X0,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f55,f85])).
% 0.21/0.53  % (6461)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (6453)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (6446)Refutation not found, incomplete strategy% (6446)------------------------------
% 0.21/0.53  % (6446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6446)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6446)Memory used [KB]: 10618
% 0.21/0.53  % (6446)Time elapsed: 0.113 s
% 0.21/0.53  % (6446)------------------------------
% 0.21/0.53  % (6446)------------------------------
% 0.21/0.53  % (6454)Refutation not found, incomplete strategy% (6454)------------------------------
% 0.21/0.53  % (6454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6454)Memory used [KB]: 1791
% 0.21/0.53  % (6454)Time elapsed: 0.116 s
% 0.21/0.53  % (6454)------------------------------
% 0.21/0.53  % (6454)------------------------------
% 0.21/0.53  % (6458)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6458)Memory used [KB]: 6140
% 0.21/0.53  % (6458)Time elapsed: 0.113 s
% 0.21/0.53  % (6458)------------------------------
% 0.21/0.53  % (6458)------------------------------
% 0.21/0.53  % (6448)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6448)Memory used [KB]: 10490
% 0.21/0.53  % (6448)Time elapsed: 0.116 s
% 0.21/0.53  % (6448)------------------------------
% 0.21/0.53  % (6448)------------------------------
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m1_subset_1(X1,X0) | r2_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f194,f40])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f43])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f192,f46])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f44])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f45])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f48])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f85])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_xboole_0(sK0) | ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f82])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_xboole_0(sK0) | ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f186,f76])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_xboole_0(sK0) | ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f181,f47])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_xboole_0(sK0) | ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | ~v8_relat_2(sK1) | ~m1_subset_1(sK2,sK0) | ~m2_filter_1(sK3,sK0,sK1) | ~r2_binop_1(sK0,sK2,sK3) | ~r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.53    inference(resolution,[],[f180,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | v1_xboole_0(X1) | ~m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0)) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | ~v8_relat_2(X0) | ~m1_subset_1(X3,X1) | ~m2_filter_1(X2,X1,X0) | ~r2_binop_1(X1,X3,X2) | ~r1_binop_1(X1,X3,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v8_relat_2(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | v1_xboole_0(X1) | ~m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0)) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~m1_subset_1(X3,X1) | ~m2_filter_1(X2,X1,X0) | ~r2_binop_1(X1,X3,X2) | ~v1_partfun1(X0,X1) | ~v3_relat_2(X0) | ~v8_relat_2(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~m1_subset_1(X3,X1) | ~m2_filter_1(X2,X1,X0) | ~r1_binop_1(X1,X3,X2) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(resolution,[],[f178,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~v1_partfun1(X1,X0) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X2,X0) | ~m2_filter_1(X3,X0,X1) | ~r1_binop_1(X0,X2,X3) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r1_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~v8_relat_2(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | v1_xboole_0(X1) | ~m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0)) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~m1_subset_1(X3,X1) | ~m2_filter_1(X2,X1,X0) | ~r2_binop_1(X1,X3,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v3_relat_2(X0) | ~v8_relat_2(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | v1_xboole_0(X1) | ~m1_subset_1(k9_eqrel_1(X1,X0,X3),k8_eqrel_1(X1,X0)) | ~r1_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~v1_partfun1(X0,X1) | r3_binop_1(k8_eqrel_1(X1,X0),k9_eqrel_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~v1_partfun1(X0,X1) | ~v3_relat_2(X0) | ~v8_relat_2(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~m1_subset_1(X3,X1) | ~m2_filter_1(X2,X1,X0) | ~r2_binop_1(X1,X3,X2) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(resolution,[],[f158,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~v1_partfun1(X1,X0) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X2,X0) | ~m2_filter_1(X3,X0,X1) | ~r2_binop_1(X0,X2,X3) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ( ! [X6,X4,X7,X5] : (~r2_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) | ~v3_relat_2(X4) | ~v8_relat_2(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_zfmisc_1(X5,X5),X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5))) | v1_xboole_0(X5) | ~m1_subset_1(X7,k8_eqrel_1(X5,X4)) | ~r1_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) | ~v1_partfun1(X4,X5) | r3_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~v1_partfun1(X1,X0) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ( ! [X6,X4,X7,X5] : (~v1_partfun1(X4,X5) | ~v3_relat_2(X4) | ~v8_relat_2(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_zfmisc_1(X5,X5),X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5))) | v1_xboole_0(X5) | ~v1_funct_2(k3_filter_1(X5,X4,X6),k2_zfmisc_1(k8_eqrel_1(X5,X4),k8_eqrel_1(X5,X4)),k8_eqrel_1(X5,X4)) | ~m1_subset_1(X7,k8_eqrel_1(X5,X4)) | ~r1_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) | ~r2_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) | r3_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_partfun1(X1,X0) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | v1_xboole_0(X0) | v1_funct_1(k3_filter_1(X0,X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X6,X4,X7,X5] : (~v1_partfun1(X4,X5) | ~v3_relat_2(X4) | ~v8_relat_2(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_zfmisc_1(X5,X5),X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5))) | v1_xboole_0(X5) | ~v1_funct_1(k3_filter_1(X5,X4,X6)) | ~v1_funct_2(k3_filter_1(X5,X4,X6),k2_zfmisc_1(k8_eqrel_1(X5,X4),k8_eqrel_1(X5,X4)),k8_eqrel_1(X5,X4)) | ~m1_subset_1(X7,k8_eqrel_1(X5,X4)) | ~r1_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) | ~r2_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6)) | r3_binop_1(k8_eqrel_1(X5,X4),X7,k3_filter_1(X5,X4,X6))) )),
% 0.21/0.53    inference(resolution,[],[f68,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m1_subset_1(X1,X0) | ~r1_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | r3_binop_1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~v1_partfun1(X1,X0) | ~v3_relat_2(X1) | ~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (6451)------------------------------
% 0.21/0.53  % (6451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6451)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (6451)Memory used [KB]: 6396
% 0.21/0.53  % (6451)Time elapsed: 0.111 s
% 0.21/0.53  % (6451)------------------------------
% 0.21/0.53  % (6451)------------------------------
% 0.21/0.54  % (6437)Success in time 0.174 s
%------------------------------------------------------------------------------
