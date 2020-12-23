%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 929 expanded)
%              Number of leaves         :   11 ( 367 expanded)
%              Depth                    :   32
%              Number of atoms          :  747 (7512 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(subsumption_resolution,[],[f246,f127])).

fof(f127,plain,(
    r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r6_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m2_filter_1(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r6_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m2_filter_1(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r6_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m2_filter_1(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                & r6_binop_1(sK0,X2,X3)
                & m2_filter_1(X3,sK0,X1) )
            & m2_filter_1(X2,sK0,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
              & r6_binop_1(sK0,X2,X3)
              & m2_filter_1(X3,sK0,sK1) )
          & m2_filter_1(X2,sK0,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v8_relat_2(sK1)
      & v3_relat_2(sK1)
      & v1_partfun1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
            & r6_binop_1(sK0,X2,X3)
            & m2_filter_1(X3,sK0,sK1) )
        & m2_filter_1(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
          & r6_binop_1(sK0,sK2,X3)
          & m2_filter_1(X3,sK0,sK1) )
      & m2_filter_1(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r6_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r6_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r6_binop_1(X0,X2,X3)
                     => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r6_binop_1(X0,X2,X3)
                   => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_filter_1)).

fof(f53,plain,
    ( v1_funct_1(sK2)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f51,f50])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,
    ( v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    m2_filter_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f126,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f125,f60])).

fof(f60,plain,(
    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f50])).

fof(f57,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f41,f34])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f36,plain,(
    r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f123,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f92,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f63,f50])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | r4_binop_1(sK0,X1,sK3)
      | ~ r6_binop_1(sK0,X1,sK3)
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f91,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f55,f29])).

fof(f55,plain,
    ( v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f52,f50])).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r6_binop_1(sK0,X1,sK3)
      | r4_binop_1(sK0,X1,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f88,f62])).

fof(f62,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f61,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f58,f50])).

fof(f58,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f41,f35])).

fof(f88,plain,(
    ! [X1] :
      ( ~ r6_binop_1(sK0,X1,sK3)
      | r4_binop_1(sK0,X1,sK3)
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f43,f68])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f50])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f35])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r6_binop_1(X0,X1,X2)
      | r4_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_binop_1)).

fof(f246,plain,(
    ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f245,f34])).

fof(f245,plain,
    ( ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f244,f35])).

fof(f244,plain,
    ( ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f243,f151])).

fof(f151,plain,(
    r5_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f150,f54])).

fof(f150,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f149,f60])).

fof(f149,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f147,f36])).

fof(f147,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f122,f66])).

fof(f122,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | r5_binop_1(sK0,X1,sK3)
      | ~ r6_binop_1(sK0,X1,sK3)
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f121,f56])).

fof(f121,plain,(
    ! [X1] :
      ( ~ r6_binop_1(sK0,X1,sK3)
      | r5_binop_1(sK0,X1,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f118,f62])).

fof(f118,plain,(
    ! [X1] :
      ( ~ r6_binop_1(sK0,X1,sK3)
      | r5_binop_1(sK0,X1,sK3)
      | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f44,f68])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r6_binop_1(X0,X1,X2)
      | r5_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f243,plain,
    ( ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f242,f54])).

fof(f242,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f241,f60])).

fof(f241,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f240,f66])).

fof(f240,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f239,f68])).

fof(f239,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f238,f33])).

fof(f238,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f237,f56])).

fof(f237,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f236,f62])).

fof(f236,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f235,f29])).

fof(f235,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f234,f30])).

fof(f30,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f234,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f233,f31])).

fof(f31,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f233,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f228,f32])).

fof(f32,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f228,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m2_filter_1(sK2,sK0,sK1)
    | ~ r4_binop_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f227,f37])).

fof(f37,plain,(
    ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f227,plain,(
    ! [X2,X0,X3,X1] :
      ( r6_binop_1(k8_eqrel_1(X1,X0),k3_filter_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(X1,X3,X2)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ m2_filter_1(X3,X1,X0)
      | ~ r4_binop_1(X1,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X2)
      | r6_binop_1(k8_eqrel_1(X1,X0),k3_filter_1(X1,X0,X3),k3_filter_1(X1,X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(X1,X3,X2)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ m2_filter_1(X3,X1,X0)
      | ~ r4_binop_1(X1,X3,X2)
      | ~ m2_filter_1(X2,X1,X0)
      | ~ m2_filter_1(X3,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f225,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r4_binop_1(X0,X2,X3)
                   => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_filter_1)).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X2)
      | v1_xboole_0(X2)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X2,X2),X2)
      | ~ v1_funct_1(X0)
      | r6_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X2,X2),X2)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(X2,X3,X0)
      | ~ m2_filter_1(X0,X2,X1)
      | ~ m2_filter_1(X3,X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X2)
      | v1_xboole_0(X2)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X2,X2),X2)
      | ~ r4_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0))
      | r6_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X2,X2),X2)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(X2,X3,X0)
      | ~ m2_filter_1(X0,X2,X1)
      | ~ m2_filter_1(X3,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f223,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r5_binop_1(X0,X2,X3)
                   => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_filter_1)).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f222,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f222,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f221,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f221,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ v1_funct_1(k3_filter_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ v1_funct_1(k3_filter_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f186,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f185,f48])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
      | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ v1_funct_1(k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
      | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r5_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | r6_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:34:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (11212)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.43  % (11212)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f247,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f246,f127])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.43    inference(subsumption_resolution,[],[f126,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    v1_funct_1(sK2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f53,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~v1_xboole_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    (((~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r6_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m2_filter_1(sK2,sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r6_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m2_filter_1(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r6_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m2_filter_1(X2,sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r6_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m2_filter_1(X2,sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) => (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r6_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m2_filter_1(X2,sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r6_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m2_filter_1(X2,sK0,sK1)) => (? [X3] : (~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r6_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) & m2_filter_1(sK2,sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ? [X3] : (~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r6_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) => (~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r6_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r6_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m2_filter_1(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r6_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m2_filter_1(X2,X0,X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r6_binop_1(X0,X2,X3) => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r6_binop_1(X0,X2,X3) => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_filter_1)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    v1_funct_1(sK2) | v1_xboole_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f51,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(resolution,[],[f46,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    v1_funct_1(sK2) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f40,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    m2_filter_1(sK2,sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | v1_funct_1(X2) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    r4_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f125,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f59,f29])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f57,f50])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f41,f34])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    r4_binop_1(sK0,sK2,sK3) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f123,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    r6_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    r4_binop_1(sK0,sK2,sK3) | ~r6_binop_1(sK0,sK2,sK3) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2)),
% 0.21/0.44    inference(resolution,[],[f92,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.44    inference(subsumption_resolution,[],[f65,f29])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f63,f50])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f42,f34])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | r4_binop_1(sK0,X1,sK3) | ~r6_binop_1(sK0,X1,sK3) | ~v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f91,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    v1_funct_1(sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f55,f29])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    v1_funct_1(sK3) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f52,f50])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    v1_funct_1(sK3) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f40,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    m2_filter_1(sK3,sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ( ! [X1] : (~r6_binop_1(sK0,X1,sK3) | r4_binop_1(sK0,X1,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f88,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f61,f29])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f58,f50])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f41,f35])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X1] : (~r6_binop_1(sK0,X1,sK3) | r4_binop_1(sK0,X1,sK3) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(resolution,[],[f43,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.44    inference(subsumption_resolution,[],[f67,f29])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f64,f50])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f42,f35])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~r6_binop_1(X0,X1,X2) | r4_binop_1(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (((r6_binop_1(X0,X1,X2) | ~r5_binop_1(X0,X1,X2) | ~r4_binop_1(X0,X1,X2)) & ((r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)) | ~r6_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1))),
% 0.21/0.44    inference(flattening,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (((r6_binop_1(X0,X1,X2) | (~r5_binop_1(X0,X1,X2) | ~r4_binop_1(X0,X1,X2))) & ((r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)) | ~r6_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((r6_binop_1(X0,X1,X2) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1))),
% 0.21/0.44    inference(flattening,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((r6_binop_1(X0,X1,X2) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r6_binop_1(X0,X1,X2) <=> (r5_binop_1(X0,X1,X2) & r4_binop_1(X0,X1,X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_binop_1)).
% 0.21/0.44  fof(f246,plain,(
% 0.21/0.44    ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f245,f34])).
% 0.21/0.44  fof(f245,plain,(
% 0.21/0.44    ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f244,f35])).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f243,f151])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    r5_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f150,f54])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    r5_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f149,f60])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    r5_binop_1(sK0,sK2,sK3) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f147,f36])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    r5_binop_1(sK0,sK2,sK3) | ~r6_binop_1(sK0,sK2,sK3) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2)),
% 0.21/0.44    inference(resolution,[],[f122,f66])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | r5_binop_1(sK0,X1,sK3) | ~r6_binop_1(sK0,X1,sK3) | ~v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f121,f56])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    ( ! [X1] : (~r6_binop_1(sK0,X1,sK3) | r5_binop_1(sK0,X1,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f118,f62])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X1] : (~r6_binop_1(sK0,X1,sK3) | r5_binop_1(sK0,X1,sK3) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(resolution,[],[f44,f68])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~r6_binop_1(X0,X1,X2) | r5_binop_1(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f242,f54])).
% 0.21/0.44  fof(f242,plain,(
% 0.21/0.44    ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f241,f60])).
% 0.21/0.44  fof(f241,plain,(
% 0.21/0.44    ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f240,f66])).
% 0.21/0.44  fof(f240,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f239,f68])).
% 0.21/0.44  fof(f239,plain,(
% 0.21/0.44    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f238,f33])).
% 0.21/0.44  fof(f238,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f237,f56])).
% 0.21/0.44  fof(f237,plain,(
% 0.21/0.44    ~v1_funct_1(sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f236,f62])).
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f235,f29])).
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    v1_xboole_0(sK0) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f234,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    v1_partfun1(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f234,plain,(
% 0.21/0.44    ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f233,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    v3_relat_2(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f228,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    v8_relat_2(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f228,plain,(
% 0.21/0.44    ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK2) | ~r5_binop_1(sK0,sK2,sK3) | ~m2_filter_1(sK3,sK0,sK1) | ~m2_filter_1(sK2,sK0,sK1) | ~r4_binop_1(sK0,sK2,sK3)),
% 0.21/0.44    inference(resolution,[],[f227,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ~r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r6_binop_1(k8_eqrel_1(X1,X0),k3_filter_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~v8_relat_2(X0) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~r5_binop_1(X1,X3,X2) | ~m2_filter_1(X2,X1,X0) | ~m2_filter_1(X3,X1,X0) | ~r4_binop_1(X1,X3,X2)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f226])).
% 0.21/0.44  fof(f226,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X0) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1) | ~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X2) | r6_binop_1(k8_eqrel_1(X1,X0),k3_filter_1(X1,X0,X3),k3_filter_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~r5_binop_1(X1,X3,X2) | ~m2_filter_1(X2,X1,X0) | ~m2_filter_1(X3,X1,X0) | ~r4_binop_1(X1,X3,X2) | ~m2_filter_1(X2,X1,X0) | ~m2_filter_1(X3,X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X0) | ~v3_relat_2(X0) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(resolution,[],[f225,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r4_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m2_filter_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r4_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r4_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r4_binop_1(X0,X2,X3) => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_filter_1)).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r4_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X2) | v1_xboole_0(X2) | ~v1_funct_2(X0,k2_zfmisc_1(X2,X2),X2) | ~v1_funct_1(X0) | r6_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) | ~v1_funct_2(X3,k2_zfmisc_1(X2,X2),X2) | ~v1_funct_1(X3) | ~r5_binop_1(X2,X3,X0) | ~m2_filter_1(X0,X2,X1) | ~m2_filter_1(X3,X2,X1)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f224])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X2) | v1_xboole_0(X2) | ~v1_funct_2(X0,k2_zfmisc_1(X2,X2),X2) | ~r4_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0)) | r6_binop_1(k8_eqrel_1(X2,X1),k3_filter_1(X2,X1,X3),k3_filter_1(X2,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) | ~v1_funct_2(X3,k2_zfmisc_1(X2,X2),X2) | ~v1_funct_1(X3) | ~r5_binop_1(X2,X3,X0) | ~m2_filter_1(X0,X2,X1) | ~m2_filter_1(X3,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X2) | v1_xboole_0(X2)) )),
% 0.21/0.44    inference(resolution,[],[f223,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r5_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m2_filter_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r5_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r5_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m2_filter_1(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r5_binop_1(X0,X2,X3) => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_filter_1)).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f222,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f221,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | v1_funct_1(k3_filter_1(X0,X1,X2)) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f221,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~v1_funct_1(k3_filter_1(X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~v1_funct_1(k3_filter_1(X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.44    inference(resolution,[],[f186,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | ~r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f185,f48])).
% 0.21/0.44  fof(f185,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | ~r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | ~v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) | ~v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f180,f47])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v8_relat_2(X2) | ~v3_relat_2(X2) | ~v1_partfun1(X2,X1) | v1_xboole_0(X1) | ~r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | ~r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0)) | ~v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~v1_funct_1(k3_filter_1(X1,X2,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) | ~v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(resolution,[],[f49,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~r5_binop_1(X0,X1,X2) | ~r4_binop_1(X0,X1,X2) | r6_binop_1(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (11212)------------------------------
% 0.21/0.44  % (11212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (11212)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (11212)Memory used [KB]: 5500
% 0.21/0.44  % (11212)Time elapsed: 0.036 s
% 0.21/0.44  % (11212)------------------------------
% 0.21/0.44  % (11212)------------------------------
% 0.21/0.44  % (11192)Success in time 0.087 s
%------------------------------------------------------------------------------
