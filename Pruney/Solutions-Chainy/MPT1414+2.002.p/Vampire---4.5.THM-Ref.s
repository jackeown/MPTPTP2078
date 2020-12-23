%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 (1292 expanded)
%              Number of leaves         :   18 ( 579 expanded)
%              Depth                    :   10
%              Number of atoms          :  452 (10740 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f88,f119,f100,f54,f89,f90,f102,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | r3_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).

fof(f102,plain,(
    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f48,f47,f51,f52,f50,f92,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r2_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_filter_1)).

fof(f92,plain,(
    r2_binop_1(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f82,f51,f53,f83,f84,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r3_binop_1(X0,X1,X2)
      | r2_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(unit_resulting_resolution,[],[f46,f52,f78,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f78,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f60,f50,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f83,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f46,f52,f78,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
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
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r3_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                & r3_binop_1(sK0,X2,X3)
                & m2_filter_1(X3,sK0,X1) )
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
              & r3_binop_1(sK0,X2,X3)
              & m2_filter_1(X3,sK0,sK1) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v8_relat_2(sK1)
      & v3_relat_2(sK1)
      & v1_partfun1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
            & r3_binop_1(sK0,X2,X3)
            & m2_filter_1(X3,sK0,sK1) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
          & r3_binop_1(sK0,sK2,X3)
          & m2_filter_1(X3,sK0,sK1) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r3_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r3_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_filter_1)).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(unit_resulting_resolution,[],[f46,f52,f78,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f47,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f48,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f49,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f46,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f46,f82,f48,f49,f47,f50,f83,f84,f74])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f89,plain,(
    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f82,f48,f49,f47,f50,f83,f84,f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f48,f47,f51,f52,f50,f91,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r1_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_filter_1)).

fof(f91,plain,(
    r1_binop_1(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f82,f51,f53,f83,f84,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r3_binop_1(X0,X1,X2)
      | r1_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f103,f86,f85,f77,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f77,plain,(
    m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f48,f49,f51,f47,f50,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(f85,plain,(
    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

fof(f76,plain,(
    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f48,f49,f47,f50,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(f86,plain,(
    ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f76,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_eqrel_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).

fof(f103,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f86,f85,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f88,plain,(
    v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f46,f82,f48,f49,f47,f50,f83,f84,f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (30327)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (30330)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (30329)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (30335)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (30337)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (30327)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (30331)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (30339)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f88,f119,f100,f54,f89,f90,f102,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | r3_binop_1(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.50    inference(flattening,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f48,f47,f51,f52,f50,f92,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_filter_1)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    r2_binop_1(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f82,f51,f53,f83,f84,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~r3_binop_1(X0,X1,X2) | r2_binop_1(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f52,f78,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f60,f50,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f52,f78,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    r3_binop_1(sK0,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    (((~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f41,f40,f39,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) => (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(X2,sK0)) => (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(sK2,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) => (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_filter_1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f52,f78,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_filter_1(X2,X0,X1) | v1_funct_1(X2) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m2_filter_1(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_subset_1(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_partfun1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v3_relat_2(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v8_relat_2(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f82,f48,f49,f47,f50,f83,f84,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f82,f48,f49,f47,f50,f83,f84,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f48,f47,f51,f52,f50,f91,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_filter_1)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    r1_binop_1(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f82,f51,f53,f83,f84,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~r3_binop_1(X0,X1,X2) | r1_binop_1(X0,X1,X2) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f103,f86,f85,f77,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_subset_1(X2,X0,X1) | m1_subset_1(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m2_subset_1(X2,X0,X1) | ~m1_subset_1(X2,X1)) & (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f48,f49,f51,f47,f50,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f76,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_eqrel_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_eqrel_1(X1,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_eqrel_1(X1,X0) => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f48,f49,f47,f50,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_eqrel_1(k8_eqrel_1(X0,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f76,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_eqrel_1(X1,X0) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | ~m1_eqrel_1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_eqrel_1(X1,X0) => ~v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f85,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    v1_funct_1(k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f82,f48,f49,f47,f50,f83,f84,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | v1_funct_1(k3_filter_1(X0,X1,X2)) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30327)------------------------------
% 0.21/0.50  % (30327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30327)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30327)Memory used [KB]: 1023
% 0.21/0.50  % (30327)Time elapsed: 0.068 s
% 0.21/0.50  % (30327)------------------------------
% 0.21/0.50  % (30327)------------------------------
% 0.21/0.50  % (30321)Success in time 0.142 s
%------------------------------------------------------------------------------
