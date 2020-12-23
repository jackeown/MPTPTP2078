%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:30 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   93 (1430 expanded)
%              Number of leaves         :   17 ( 644 expanded)
%              Depth                    :   11
%              Number of atoms          :  478 (12231 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (6175)Refutation not found, incomplete strategy% (6175)------------------------------
% (6175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6175)Termination reason: Refutation not found, incomplete strategy

% (6175)Memory used [KB]: 10490
% (6175)Time elapsed: 0.120 s
% (6175)------------------------------
% (6175)------------------------------
fof(f252,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f47,f77,f49,f50,f48,f51,f81,f102,f237,f74])).

% (6182)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(flattening,[],[f37])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f237,plain,(
    ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f204,f179,f55,f230,f220,f236,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f236,plain,(
    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f77,f49,f50,f48,f51,f81,f102,f73])).

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
    inference(cnf_transformation,[],[f38])).

% (6185)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f220,plain,(
    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f49,f48,f52,f169,f53,f51,f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f53,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f42,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
    ( ? [X3] :
        ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r3_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r3_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f169,plain,(
    r1_binop_1(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f77,f52,f54,f81,f102,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f54,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f52,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f230,plain,(
    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f49,f48,f52,f173,f53,f51,f57])).

fof(f57,plain,(
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
                 => ( r2_binop_1(X0,X2,X3)
                   => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).

fof(f173,plain,(
    r2_binop_1(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f77,f52,f54,f81,f102,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | r2_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f179,plain,(
    m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f159,f147,f157,f177,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f177,plain,(
    m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f49,f50,f52,f48,f51,f71])).

% (6172)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (6181)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (6185)Refutation not found, incomplete strategy% (6185)------------------------------
% (6185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6185)Termination reason: Refutation not found, incomplete strategy

% (6185)Memory used [KB]: 6140
% (6185)Time elapsed: 0.124 s
% (6185)------------------------------
% (6185)------------------------------
% (6172)Refutation not found, incomplete strategy% (6172)------------------------------
% (6172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6172)Termination reason: Refutation not found, incomplete strategy

% (6172)Memory used [KB]: 6140
% (6172)Time elapsed: 0.119 s
% (6172)------------------------------
% (6172)------------------------------
% (6177)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (6173)Refutation not found, incomplete strategy% (6173)------------------------------
% (6173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6173)Termination reason: Refutation not found, incomplete strategy

% (6173)Memory used [KB]: 10618
% (6173)Time elapsed: 0.087 s
% (6173)------------------------------
% (6173)------------------------------
% (6171)Refutation not found, incomplete strategy% (6171)------------------------------
% (6171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6171)Termination reason: Refutation not found, incomplete strategy

% (6171)Memory used [KB]: 10746
% (6171)Time elapsed: 0.087 s
% (6171)------------------------------
% (6171)------------------------------
% (6180)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (6181)Refutation not found, incomplete strategy% (6181)------------------------------
% (6181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6181)Termination reason: Refutation not found, incomplete strategy

% (6181)Memory used [KB]: 1663
% (6181)Time elapsed: 0.098 s
% (6181)------------------------------
% (6181)------------------------------
% (6184)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (6178)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(f157,plain,(
    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(forward_demodulation,[],[f155,f142])).

fof(f142,plain,(
    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f49,f50,f48,f51,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(f155,plain,(
    m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f49,f50,f48,f51,f69])).

% (6188)Refutation not found, incomplete strategy% (6188)------------------------------
% (6188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6188)Termination reason: Refutation not found, incomplete strategy

% (6188)Memory used [KB]: 10874
% (6188)Time elapsed: 0.144 s
% (6188)------------------------------
% (6188)------------------------------
fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(f147,plain,(
    ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f130,f142])).

fof(f130,plain,(
    ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f49,f50,f48,f51,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_eqrel_1)).

fof(f159,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f147,f157,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f204,plain,(
    v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f49,f77,f48,f51,f81,f102,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f75,f53,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ m2_filter_1(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f75,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f51,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f81,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f75,f53,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ m2_filter_1(X2,X0,X1)
      | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f48,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f50,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f49,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(unit_resulting_resolution,[],[f47,f53,f75,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ m2_filter_1(X2,X0,X1)
      | v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (6168)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (6168)Refutation not found, incomplete strategy% (6168)------------------------------
% 0.20/0.50  % (6168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6169)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (6168)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6168)Memory used [KB]: 10618
% 0.20/0.50  % (6168)Time elapsed: 0.079 s
% 0.20/0.50  % (6168)------------------------------
% 0.20/0.50  % (6168)------------------------------
% 0.20/0.51  % (6179)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (6176)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (6167)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (6171)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (6187)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.25/0.52  % (6183)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.25/0.52  % (6170)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.25/0.53  % (6173)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.25/0.53  % (6166)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.25/0.53  % (6174)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.25/0.53  % (6165)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.25/0.53  % (6186)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.25/0.53  % (6188)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.25/0.53  % (6175)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.25/0.53  % (6179)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  % (6175)Refutation not found, incomplete strategy% (6175)------------------------------
% 1.25/0.53  % (6175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (6175)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (6175)Memory used [KB]: 10490
% 1.25/0.53  % (6175)Time elapsed: 0.120 s
% 1.25/0.53  % (6175)------------------------------
% 1.25/0.53  % (6175)------------------------------
% 1.25/0.53  fof(f252,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f47,f77,f49,f50,f48,f51,f81,f102,f237,f74])).
% 1.25/0.53  % (6182)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.25/0.53  fof(f74,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v8_relat_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 1.25/0.53    inference(flattening,[],[f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).
% 1.25/0.53  fof(f237,plain,(
% 1.25/0.53    ~m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f204,f179,f55,f230,f220,f236,f61])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | r3_binop_1(X0,X1,X2) | ~m1_subset_1(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f45])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.25/0.53    inference(flattening,[],[f44])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.25/0.53    inference(nnf_transformation,[],[f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 1.25/0.53    inference(flattening,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).
% 1.25/0.53  fof(f236,plain,(
% 1.25/0.53    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f47,f77,f49,f50,f48,f51,f81,f102,f73])).
% 1.25/0.53  fof(f73,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f38])).
% 1.25/0.53  % (6185)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.25/0.53  fof(f220,plain,(
% 1.25/0.53    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f47,f50,f49,f48,f52,f169,f53,f51,f56])).
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.25/0.53    inference(flattening,[],[f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).
% 1.25/0.53  fof(f53,plain,(
% 1.25/0.53    m2_filter_1(sK3,sK0,sK1)),
% 1.25/0.53    inference(cnf_transformation,[],[f43])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    (((~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f42,f41,f40,f39])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) => (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(X2,sK0)) => (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(sK2,sK0))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f42,plain,(
% 1.25/0.53    ? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) => (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.25/0.53    inference(flattening,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f14])).
% 1.25/0.53  fof(f14,negated_conjecture,(
% 1.25/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.25/0.53    inference(negated_conjecture,[],[f13])).
% 1.25/0.53  fof(f13,conjecture,(
% 1.25/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).
% 1.25/0.53  fof(f169,plain,(
% 1.25/0.53    r1_binop_1(sK0,sK2,sK3)),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f77,f52,f54,f81,f102,f59])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | r1_binop_1(X0,X1,X2) | ~m1_subset_1(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f45])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    r3_binop_1(sK0,sK2,sK3)),
% 1.25/0.53    inference(cnf_transformation,[],[f43])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    m1_subset_1(sK2,sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f43])).
% 1.25/0.53  fof(f230,plain,(
% 1.25/0.53    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f47,f50,f49,f48,f52,f173,f53,f51,f57])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.25/0.53    inference(flattening,[],[f19])).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f12])).
% 1.25/0.53  fof(f12,axiom,(
% 1.25/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).
% 1.25/0.53  fof(f173,plain,(
% 1.25/0.53    r2_binop_1(sK0,sK2,sK3)),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f77,f52,f54,f81,f102,f60])).
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | r2_binop_1(X0,X1,X2) | ~m1_subset_1(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f45])).
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.25/0.53    inference(cnf_transformation,[],[f43])).
% 1.25/0.53  fof(f179,plain,(
% 1.25/0.53    m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f159,f147,f157,f177,f62])).
% 1.25/0.54  fof(f62,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m2_subset_1(X2,X0,X1) | m1_subset_1(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f46])).
% 1.25/0.54  fof(f46,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : ((m2_subset_1(X2,X0,X1) | ~m1_subset_1(X2,X1)) & (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.25/0.54    inference(nnf_transformation,[],[f25])).
% 1.25/0.54  fof(f25,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.25/0.54    inference(flattening,[],[f24])).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).
% 1.25/0.54  fof(f177,plain,(
% 1.25/0.54    m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f47,f49,f50,f52,f48,f51,f71])).
% 1.25/0.54  % (6172)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.25/0.54  % (6181)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.25/0.54  % (6185)Refutation not found, incomplete strategy% (6185)------------------------------
% 1.25/0.54  % (6185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (6185)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (6185)Memory used [KB]: 6140
% 1.25/0.54  % (6185)Time elapsed: 0.124 s
% 1.25/0.54  % (6185)------------------------------
% 1.25/0.54  % (6185)------------------------------
% 1.25/0.54  % (6172)Refutation not found, incomplete strategy% (6172)------------------------------
% 1.25/0.54  % (6172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (6172)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (6172)Memory used [KB]: 6140
% 1.25/0.54  % (6172)Time elapsed: 0.119 s
% 1.25/0.54  % (6172)------------------------------
% 1.25/0.54  % (6172)------------------------------
% 1.25/0.54  % (6177)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.25/0.54  % (6173)Refutation not found, incomplete strategy% (6173)------------------------------
% 1.25/0.54  % (6173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (6173)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (6173)Memory used [KB]: 10618
% 1.25/0.54  % (6173)Time elapsed: 0.087 s
% 1.25/0.54  % (6173)------------------------------
% 1.25/0.54  % (6173)------------------------------
% 1.25/0.54  % (6171)Refutation not found, incomplete strategy% (6171)------------------------------
% 1.25/0.54  % (6171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (6171)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (6171)Memory used [KB]: 10746
% 1.25/0.54  % (6171)Time elapsed: 0.087 s
% 1.25/0.54  % (6171)------------------------------
% 1.25/0.54  % (6171)------------------------------
% 1.41/0.54  % (6180)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.41/0.54  % (6181)Refutation not found, incomplete strategy% (6181)------------------------------
% 1.41/0.54  % (6181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (6181)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (6181)Memory used [KB]: 1663
% 1.41/0.54  % (6181)Time elapsed: 0.098 s
% 1.41/0.54  % (6181)------------------------------
% 1.41/0.54  % (6181)------------------------------
% 1.41/0.54  % (6184)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.41/0.55  % (6178)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(flattening,[],[f35])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).
% 1.41/0.55  fof(f157,plain,(
% 1.41/0.55    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.41/0.55    inference(forward_demodulation,[],[f155,f142])).
% 1.41/0.55  fof(f142,plain,(
% 1.41/0.55    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f49,f50,f48,f51,f68])).
% 1.41/0.55  fof(f68,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~v3_relat_2(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.41/0.55    inference(flattening,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).
% 1.41/0.55  fof(f155,plain,(
% 1.41/0.55    m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f49,f50,f48,f51,f69])).
% 1.41/0.55  % (6188)Refutation not found, incomplete strategy% (6188)------------------------------
% 1.41/0.55  % (6188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (6188)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (6188)Memory used [KB]: 10874
% 1.41/0.55  % (6188)Time elapsed: 0.144 s
% 1.41/0.55  % (6188)------------------------------
% 1.41/0.55  % (6188)------------------------------
% 1.41/0.55  fof(f69,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v8_relat_2(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_relat_2(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.41/0.55    inference(flattening,[],[f32])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).
% 1.41/0.55  fof(f147,plain,(
% 1.41/0.55    ~v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 1.41/0.55    inference(backward_demodulation,[],[f130,f142])).
% 1.41/0.55  fof(f130,plain,(
% 1.41/0.55    ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f47,f49,f50,f48,f51,f67])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(flattening,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k7_eqrel_1(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_eqrel_1)).
% 1.41/0.55  fof(f159,plain,(
% 1.41/0.55    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f147,f157,f58])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f21])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.41/0.55  fof(f204,plain,(
% 1.41/0.55    v1_funct_1(k3_filter_1(sK0,sK1,sK3))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f47,f50,f49,f77,f48,f51,f81,f102,f72])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~v8_relat_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k3_filter_1(X0,X1,X2)) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f38])).
% 1.41/0.55  fof(f102,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f47,f75,f53,f66])).
% 1.41/0.55  fof(f66,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~m2_filter_1(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(flattening,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).
% 1.41/0.55  fof(f75,plain,(
% 1.41/0.55    v1_relat_1(sK1)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f51,f70])).
% 1.41/0.55  fof(f70,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.55  fof(f81,plain,(
% 1.41/0.55    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f47,f75,f53,f65])).
% 1.41/0.55  fof(f65,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~m2_filter_1(X2,X0,X1) | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f27])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    v1_partfun1(sK1,sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    v8_relat_2(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    v3_relat_2(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f77,plain,(
% 1.41/0.55    v1_funct_1(sK3)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f47,f53,f75,f64])).
% 1.41/0.55  fof(f64,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~m2_filter_1(X2,X0,X1) | v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f27])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ~v1_xboole_0(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (6179)------------------------------
% 1.41/0.55  % (6179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (6179)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (6179)Memory used [KB]: 10874
% 1.41/0.55  % (6179)Time elapsed: 0.080 s
% 1.41/0.55  % (6179)------------------------------
% 1.41/0.55  % (6179)------------------------------
% 1.41/0.56  % (6162)Success in time 0.192 s
%------------------------------------------------------------------------------
