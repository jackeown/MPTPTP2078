%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  173 (1499 expanded)
%              Number of leaves         :   19 ( 619 expanded)
%              Depth                    :   21
%              Number of atoms          :  797 (11952 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f529,plain,(
    $false ),
    inference(subsumption_resolution,[],[f528,f402])).

fof(f402,plain,(
    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f399,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f45,f44,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
    ( ? [X3] :
        ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r3_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r3_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

% (15103)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f15,conjecture,(
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

fof(f399,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f390,f197])).

fof(f197,plain,(
    ! [X1] :
      ( ~ r2_binop_1(sK0,X1,sK3)
      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f196,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f196,plain,(
    ! [X1] :
      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3))
      | ~ r2_binop_1(sK0,X1,sK3)
      | ~ m1_subset_1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f51])).

fof(f51,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f195,plain,(
    ! [X1] :
      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3))
      | ~ r2_binop_1(sK0,X1,sK3)
      | ~ m1_subset_1(X1,sK0)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f52])).

fof(f52,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f194,plain,(
    ! [X1] :
      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3))
      | ~ r2_binop_1(sK0,X1,sK3)
      | ~ m1_subset_1(X1,sK0)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f53])).

fof(f53,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f193,plain,(
    ! [X1] :
      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3))
      | ~ r2_binop_1(sK0,X1,sK3)
      | ~ m1_subset_1(X1,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f54])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f184,plain,(
    ! [X1] :
      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3))
      | ~ r2_binop_1(sK0,X1,sK3)
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f56,f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f56,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f390,plain,(
    r2_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f389,f251])).

fof(f251,plain,(
    v1_funct_1(sK3) ),
    inference(resolution,[],[f185,f227])).

fof(f227,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f214,f63])).

% (15104)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f214,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f54,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
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

fof(f185,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f180,f50])).

fof(f180,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f56,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f389,plain,
    ( r2_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f387,f273])).

fof(f273,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(resolution,[],[f187,f227])).

fof(f187,plain,
    ( ~ v1_relat_1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(subsumption_resolution,[],[f182,f50])).

fof(f182,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f56,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f387,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r2_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f201,f271])).

fof(f271,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(resolution,[],[f186,f227])).

fof(f186,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f181,f50])).

fof(f181,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f201,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r2_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f199,f55])).

fof(f199,plain,
    ( r2_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).

fof(f57,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f528,plain,(
    ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f527,f397])).

fof(f397,plain,(
    v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f396,f251])).

fof(f396,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f392,f273])).

fof(f392,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f159,f271])).

fof(f159,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | v1_funct_1(k3_filter_1(sK0,sK1,X5))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,sK1,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f52])).

fof(f157,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,sK1,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X5)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f156,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,sK1,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X5)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f54])).

fof(f130,plain,(
    ! [X5] :
      ( v1_funct_1(k3_filter_1(sK0,sK1,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f51,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f527,plain,
    ( ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f526,f434])).

% (15082)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f434,plain,(
    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f433,f251])).

fof(f433,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f429,f273])).

fof(f429,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f163,f271])).

fof(f163,plain,(
    ! [X6] :
      ( ~ v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f162,f50])).

fof(f162,plain,(
    ! [X6] :
      ( v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f52])).

fof(f161,plain,(
    ! [X6] :
      ( v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X6)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f53])).

fof(f160,plain,(
    ! [X6] :
      ( v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X6)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f54])).

fof(f131,plain,(
    ! [X6] :
      ( v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f51,f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f526,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f525,f443])).

% (15095)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (15084)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (15086)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (15088)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% (15091)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (15085)Refutation not found, incomplete strategy% (15085)------------------------------
% (15085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15085)Termination reason: Refutation not found, incomplete strategy

% (15085)Memory used [KB]: 10618
% (15085)Time elapsed: 0.102 s
% (15085)------------------------------
% (15085)------------------------------
% (15097)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f443,plain,(
    m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f442,f251])).

fof(f442,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f438,f273])).

fof(f438,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f167,f271])).

fof(f167,plain,(
    ! [X7] :
      ( ~ v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,(
    ! [X7] :
      ( m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X7)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f52])).

fof(f165,plain,(
    ! [X7] :
      ( m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X7)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f53])).

fof(f164,plain,(
    ! [X7] :
      ( m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X7)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f132,plain,(
    ! [X7] :
      ( m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f51,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f525,plain,
    ( ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f517,f384])).

fof(f384,plain,(
    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f381,f55])).

fof(f381,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f380,f192])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r1_binop_1(sK0,X0,sK3)
      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f191,f50])).

fof(f191,plain,(
    ! [X0] :
      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f51])).

fof(f190,plain,(
    ! [X0] :
      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f189,f52])).

fof(f189,plain,(
    ! [X0] :
      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f188,f53])).

fof(f188,plain,(
    ! [X0] :
      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f54])).

fof(f183,plain,(
    ! [X0] :
      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
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
                 => ( r1_binop_1(X0,X2,X3)
                   => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_filter_1)).

fof(f380,plain,(
    r1_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f379,f251])).

fof(f379,plain,
    ( r1_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f377,f273])).

fof(f377,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r1_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f200,f271])).

fof(f200,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r1_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f55])).

fof(f198,plain,
    ( r1_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f57,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f517,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f512,f229])).

fof(f229,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f58,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f512,plain,(
    m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    inference(resolution,[],[f327,f55])).

fof(f327,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f326,f322])).

fof(f322,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f311,f151])).

fof(f151,plain,(
    ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f144,f150])).

fof(f150,plain,(
    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f149,f52])).

fof(f149,plain,
    ( k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f148,f53])).

fof(f148,plain,
    ( k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,
    ( k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(f144,plain,(
    ~ v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f143,f50])).

fof(f143,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f52])).

fof(f142,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f141,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,
    ( ~ v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_eqrel_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k7_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_eqrel_1)).

fof(f311,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f253,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
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

fof(f253,plain,(
    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f147,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

fof(f147,plain,(
    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f146,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f127,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
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
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(f326,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f325,f151])).

fof(f325,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f324,f253])).

fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f155,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f155,plain,(
    ! [X4] :
      ( m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(subsumption_resolution,[],[f154,f50])).

fof(f154,plain,(
    ! [X4] :
      ( m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X4,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f52])).

fof(f153,plain,(
    ! [X4] :
      ( m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X4,sK0)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f53])).

% (15102)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f152,plain,(
    ! [X4] :
      ( m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X4,sK0)
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,(
    ! [X4] :
      ( m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X4,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v8_relat_2(sK1)
      | ~ v3_relat_2(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:05:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (15093)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (15100)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (15087)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (15085)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (15093)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f529,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f528,f402])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f399,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    m1_subset_1(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    (((~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1)) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f45,f44,f43,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,X1)) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,sK0)) => (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v8_relat_2(sK1) & v3_relat_2(sK1) & v1_partfun1(sK1,sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,X2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(X2,sK0)) => (? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) & m1_subset_1(sK2,sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ? [X3] : (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3)) & r3_binop_1(sK0,sK2,X3) & m2_filter_1(X3,sK0,sK1)) => (~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) & r3_binop_1(sK0,sK2,sK3) & m2_filter_1(sK3,sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) & r3_binop_1(X0,X2,X3)) & m2_filter_1(X3,X0,X1)) & m1_subset_1(X2,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  % (15103)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r3_binop_1(X0,X2,X3) => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_filter_1)).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.51    inference(resolution,[],[f390,f197])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_binop_1(sK0,X1,sK3) | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) | ~m1_subset_1(X1,sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ( ! [X1] : (r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(sK0,X1,sK3) | ~m1_subset_1(X1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f195,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_partfun1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X1] : (r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(sK0,X1,sK3) | ~m1_subset_1(X1,sK0) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f194,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v3_relat_2(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ( ! [X1] : (r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(sK0,X1,sK3) | ~m1_subset_1(X1,sK0) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v8_relat_2(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X1] : (r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(sK0,X1,sK3) | ~m1_subset_1(X1,sK0) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ( ! [X1] : (r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(sK0,X1,sK3) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f56,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r2_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r2_binop_1(X0,X2,X3) => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_filter_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    m2_filter_1(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    r2_binop_1(sK0,sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f389,f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f185,f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f214,f63])).
% 0.21/0.51  % (15104)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.51    inference(resolution,[],[f54,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f180,f50])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f56,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) | ~m2_filter_1(X2,X0,X1)) | (~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_relat_1(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_filter_1(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    r2_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f387,f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.51    inference(resolution,[],[f187,f227])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f182,f50])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f56,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | r2_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f201,f271])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.51    inference(resolution,[],[f186,f227])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f50])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_relat_1(sK1) | v1_xboole_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f56,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~m2_filter_1(X2,X0,X1) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | r2_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f199,f55])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    r2_binop_1(sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.51    inference(resolution,[],[f57,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.51    inference(flattening,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((r3_binop_1(X0,X1,X2) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~r3_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    r3_binop_1(sK0,sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f528,plain,(
% 0.21/0.51    ~r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f527,f397])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    v1_funct_1(k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f396,f251])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f392,f273])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f159,f271])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_funct_1(k3_filter_1(sK0,sK1,X5)) | ~v1_funct_1(X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f50])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X5] : (v1_funct_1(k3_filter_1(sK0,sK1,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X5) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f157,f52])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X5] : (v1_funct_1(k3_filter_1(sK0,sK1,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X5) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f156,f53])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X5] : (v1_funct_1(k3_filter_1(sK0,sK1,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X5) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f54])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X5] : (v1_funct_1(k3_filter_1(sK0,sK1,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X5) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f51,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_1(k3_filter_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0) & ~v1_xboole_0(X0)) => (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) & v1_funct_1(k3_filter_1(X0,X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).
% 0.21/0.51  fof(f527,plain,(
% 0.21/0.51    ~v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f526,f434])).
% 0.21/0.51  % (15082)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f433,f251])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f429,f273])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f163,f271])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X6] : (~v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(X6)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f162,f50])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ( ! [X6] : (v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X6) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f52])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X6] : (v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X6) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f160,f53])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X6] : (v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X6) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f54])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X6] : (v1_funct_2(k3_filter_1(sK0,sK1,X6),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X6) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f51,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f526,plain,(
% 0.21/0.51    ~v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f525,f443])).
% 0.21/0.51  % (15095)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (15084)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (15086)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (15088)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.20/0.52  % (15091)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.20/0.52  % (15085)Refutation not found, incomplete strategy% (15085)------------------------------
% 1.20/0.52  % (15085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (15085)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (15085)Memory used [KB]: 10618
% 1.20/0.52  % (15085)Time elapsed: 0.102 s
% 1.20/0.52  % (15085)------------------------------
% 1.20/0.52  % (15085)------------------------------
% 1.20/0.52  % (15097)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.20/0.52  fof(f443,plain,(
% 1.20/0.52    m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))),
% 1.20/0.52    inference(subsumption_resolution,[],[f442,f251])).
% 1.20/0.52  fof(f442,plain,(
% 1.20/0.52    m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~v1_funct_1(sK3)),
% 1.20/0.52    inference(subsumption_resolution,[],[f438,f273])).
% 1.20/0.52  fof(f438,plain,(
% 1.20/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~v1_funct_1(sK3)),
% 1.20/0.52    inference(resolution,[],[f167,f271])).
% 1.20/0.52  fof(f167,plain,(
% 1.20/0.52    ( ! [X7] : (~v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~v1_funct_1(X7)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f166,f50])).
% 1.20/0.52  fof(f166,plain,(
% 1.20/0.52    ( ! [X7] : (m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X7) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f165,f52])).
% 1.20/0.52  fof(f165,plain,(
% 1.20/0.52    ( ! [X7] : (m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X7) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f164,f53])).
% 1.20/0.52  fof(f164,plain,(
% 1.20/0.52    ( ! [X7] : (m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X7) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f132,f54])).
% 1.20/0.52  fof(f132,plain,(
% 1.20/0.52    ( ! [X7] : (m1_subset_1(k3_filter_1(sK0,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(X7,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(X7) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(resolution,[],[f51,f79])).
% 1.20/0.52  fof(f79,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f41])).
% 1.20/0.52  fof(f525,plain,(
% 1.20/0.52    ~m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(subsumption_resolution,[],[f517,f384])).
% 1.20/0.52  fof(f384,plain,(
% 1.20/0.52    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(subsumption_resolution,[],[f381,f55])).
% 1.20/0.52  fof(f381,plain,(
% 1.20/0.52    r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) | ~m1_subset_1(sK2,sK0)),
% 1.20/0.52    inference(resolution,[],[f380,f192])).
% 1.20/0.52  fof(f192,plain,(
% 1.20/0.52    ( ! [X0] : (~r1_binop_1(sK0,X0,sK3) | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) | ~m1_subset_1(X0,sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f191,f50])).
% 1.20/0.52  fof(f191,plain,(
% 1.20/0.52    ( ! [X0] : (r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) | ~r1_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f190,f51])).
% 1.20/0.52  fof(f190,plain,(
% 1.20/0.52    ( ! [X0] : (r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) | ~r1_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f189,f52])).
% 1.20/0.52  fof(f189,plain,(
% 1.20/0.52    ( ! [X0] : (r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) | ~r1_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f188,f53])).
% 1.20/0.52  fof(f188,plain,(
% 1.20/0.52    ( ! [X0] : (r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) | ~r1_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f183,f54])).
% 1.20/0.52  fof(f183,plain,(
% 1.20/0.52    ( ! [X0] : (r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) | ~r1_binop_1(sK0,X0,sK3) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | ~v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 1.20/0.52    inference(resolution,[],[f56,f60])).
% 1.20/0.52  fof(f60,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0) | v1_xboole_0(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0)) | v1_xboole_0(X0))),
% 1.20/0.52    inference(flattening,[],[f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) | ~r1_binop_1(X0,X2,X3)) | ~m2_filter_1(X3,X0,X1)) | ~m1_subset_1(X2,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | ~v1_partfun1(X1,X0))) | v1_xboole_0(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,axiom,(
% 1.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(X1) & v3_relat_2(X1) & v1_partfun1(X1,X0)) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m2_filter_1(X3,X0,X1) => (r1_binop_1(X0,X2,X3) => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)))))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_filter_1)).
% 1.20/0.52  fof(f380,plain,(
% 1.20/0.52    r1_binop_1(sK0,sK2,sK3)),
% 1.20/0.52    inference(subsumption_resolution,[],[f379,f251])).
% 1.20/0.52  fof(f379,plain,(
% 1.20/0.52    r1_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK3)),
% 1.20/0.52    inference(subsumption_resolution,[],[f377,f273])).
% 1.20/0.52  fof(f377,plain,(
% 1.20/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | r1_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK3)),
% 1.20/0.52    inference(resolution,[],[f200,f271])).
% 1.20/0.52  fof(f200,plain,(
% 1.20/0.52    ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | r1_binop_1(sK0,sK2,sK3) | ~v1_funct_1(sK3)),
% 1.20/0.52    inference(subsumption_resolution,[],[f198,f55])).
% 1.20/0.52  fof(f198,plain,(
% 1.20/0.52    r1_binop_1(sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) | ~v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,sK0)),
% 1.20/0.52    inference(resolution,[],[f57,f65])).
% 1.20/0.52  fof(f65,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (r1_binop_1(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f48])).
% 1.20/0.52  fof(f517,plain,(
% 1.20/0.52    ~r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) | ~m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(resolution,[],[f512,f229])).
% 1.20/0.52  fof(f229,plain,(
% 1.20/0.52    ~m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) | ~r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) | ~m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) | ~v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) | ~v1_funct_1(k3_filter_1(sK0,sK1,sK3)) | ~r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(resolution,[],[f58,f67])).
% 1.20/0.52  fof(f67,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (r3_binop_1(X0,X1,X2) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f48])).
% 1.20/0.52  fof(f58,plain,(
% 1.20/0.52    ~r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(cnf_transformation,[],[f46])).
% 1.20/0.52  fof(f512,plain,(
% 1.20/0.52    m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))),
% 1.20/0.52    inference(resolution,[],[f327,f55])).
% 1.20/0.52  fof(f327,plain,(
% 1.20/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f326,f322])).
% 1.20/0.52  fof(f322,plain,(
% 1.20/0.52    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.20/0.52    inference(subsumption_resolution,[],[f311,f151])).
% 1.20/0.52  fof(f151,plain,(
% 1.20/0.52    ~v1_xboole_0(k8_eqrel_1(sK0,sK1))),
% 1.20/0.52    inference(backward_demodulation,[],[f144,f150])).
% 1.20/0.52  fof(f150,plain,(
% 1.20/0.52    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)),
% 1.20/0.52    inference(subsumption_resolution,[],[f149,f52])).
% 1.20/0.52  fof(f149,plain,(
% 1.20/0.52    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) | ~v3_relat_2(sK1)),
% 1.20/0.52    inference(subsumption_resolution,[],[f148,f53])).
% 1.20/0.52  fof(f148,plain,(
% 1.20/0.52    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1)),
% 1.20/0.52    inference(subsumption_resolution,[],[f128,f54])).
% 1.20/0.52  fof(f128,plain,(
% 1.20/0.52    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1)),
% 1.20/0.52    inference(resolution,[],[f51,f75])).
% 1.20/0.52  fof(f75,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f37])).
% 1.20/0.52  fof(f37,plain,(
% 1.20/0.52    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.20/0.52    inference(flattening,[],[f36])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ! [X0,X1] : (k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f12])).
% 1.20/0.52  fof(f12,axiom,(
% 1.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).
% 1.20/0.52  fof(f144,plain,(
% 1.20/0.52    ~v1_xboole_0(k7_eqrel_1(sK0,sK1))),
% 1.20/0.52    inference(subsumption_resolution,[],[f143,f50])).
% 1.20/0.52  fof(f143,plain,(
% 1.20/0.52    ~v1_xboole_0(k7_eqrel_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 1.20/0.52    inference(subsumption_resolution,[],[f142,f52])).
% 1.20/0.52  fof(f142,plain,(
% 1.20/0.52    ~v1_xboole_0(k7_eqrel_1(sK0,sK1)) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)),
% 1.20/0.52    inference(subsumption_resolution,[],[f141,f53])).
% 1.20/0.52  fof(f141,plain,(
% 1.20/0.52    ~v1_xboole_0(k7_eqrel_1(sK0,sK1)) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)),
% 1.20/0.52    inference(subsumption_resolution,[],[f126,f54])).
% 1.20/0.52  fof(f126,plain,(
% 1.20/0.52    ~v1_xboole_0(k7_eqrel_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)),
% 1.20/0.52    inference(resolution,[],[f51,f70])).
% 1.20/0.52  fof(f70,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f31])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.20/0.52    inference(flattening,[],[f30])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ! [X0,X1] : (~v1_xboole_0(k7_eqrel_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,axiom,(
% 1.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k7_eqrel_1(X0,X1)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_eqrel_1)).
% 1.20/0.52  fof(f311,plain,(
% 1.20/0.52    v1_xboole_0(k8_eqrel_1(sK0,sK1)) | ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.20/0.52    inference(resolution,[],[f253,f62])).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.20/0.52  fof(f253,plain,(
% 1.20/0.52    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.20/0.52    inference(resolution,[],[f147,f64])).
% 1.20/0.52  fof(f64,plain,(
% 1.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_eqrel_1(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f25])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_eqrel_1(X1,X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f9])).
% 1.20/0.52  fof(f9,axiom,(
% 1.20/0.52    ! [X0,X1] : (m1_eqrel_1(X1,X0) => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).
% 1.20/0.52  fof(f147,plain,(
% 1.20/0.52    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)),
% 1.20/0.52    inference(subsumption_resolution,[],[f146,f52])).
% 1.20/0.52  fof(f146,plain,(
% 1.20/0.52    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) | ~v3_relat_2(sK1)),
% 1.20/0.52    inference(subsumption_resolution,[],[f145,f53])).
% 1.20/0.52  fof(f145,plain,(
% 1.20/0.52    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1)),
% 1.20/0.52    inference(subsumption_resolution,[],[f127,f54])).
% 1.20/0.52  fof(f127,plain,(
% 1.20/0.52    m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1)),
% 1.20/0.52    inference(resolution,[],[f51,f74])).
% 1.20/0.52  fof(f74,plain,(
% 1.20/0.52    ( ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f35])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1))),
% 1.20/0.53    inference(flattening,[],[f34])).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    ! [X0,X1] : (m1_eqrel_1(k8_eqrel_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f7])).
% 1.20/0.53  fof(f7,axiom,(
% 1.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1)) => m1_eqrel_1(k8_eqrel_1(X0,X1),X0))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).
% 1.20/0.53  fof(f326,plain,(
% 1.20/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f325,f151])).
% 1.20/0.53  fof(f325,plain,(
% 1.20/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1)) | v1_xboole_0(k8_eqrel_1(sK0,sK1)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f324,f253])).
% 1.20/0.53  fof(f324,plain,(
% 1.20/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(k8_eqrel_1(sK0,sK1)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 1.20/0.53    inference(resolution,[],[f155,f68])).
% 1.20/0.53  fof(f68,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f49])).
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ! [X0,X1] : (! [X2] : ((m2_subset_1(X2,X0,X1) | ~m1_subset_1(X2,X1)) & (m1_subset_1(X2,X1) | ~m2_subset_1(X2,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.20/0.53    inference(nnf_transformation,[],[f29])).
% 1.20/0.53  fof(f29,plain,(
% 1.20/0.53    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.20/0.53    inference(flattening,[],[f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    ! [X0,X1] : (! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m2_subset_1(X2,X0,X1) <=> m1_subset_1(X2,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).
% 1.20/0.53  fof(f155,plain,(
% 1.20/0.53    ( ! [X4] : (m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X4,sK0)) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f154,f50])).
% 1.20/0.53  fof(f154,plain,(
% 1.20/0.53    ( ! [X4] : (m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X4,sK0) | v1_xboole_0(sK0)) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f153,f52])).
% 1.20/0.53  fof(f153,plain,(
% 1.20/0.53    ( ! [X4] : (m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X4,sK0) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f152,f53])).
% 1.20/0.53  % (15102)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.20/0.53  fof(f152,plain,(
% 1.20/0.53    ( ! [X4] : (m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X4,sK0) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f129,f54])).
% 1.20/0.53  fof(f129,plain,(
% 1.20/0.53    ( ! [X4] : (m2_subset_1(k9_eqrel_1(sK0,sK1,X4),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) | ~m1_subset_1(X4,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v8_relat_2(sK1) | ~v3_relat_2(sK1) | v1_xboole_0(sK0)) )),
% 1.20/0.53    inference(resolution,[],[f51,f76])).
% 1.20/0.53  fof(f76,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f39])).
% 1.20/0.53  fof(f39,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0))),
% 1.20/0.53    inference(flattening,[],[f38])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_partfun1(X1,X0) | ~v8_relat_2(X1) | ~v3_relat_2(X1) | v1_xboole_0(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f8])).
% 1.20/0.53  fof(f8,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(X1,X0) & v8_relat_2(X1) & v3_relat_2(X1) & ~v1_xboole_0(X0)) => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (15093)------------------------------
% 1.20/0.53  % (15093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (15093)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (15093)Memory used [KB]: 2046
% 1.20/0.53  % (15093)Time elapsed: 0.083 s
% 1.20/0.53  % (15093)------------------------------
% 1.20/0.53  % (15093)------------------------------
% 1.20/0.53  % (15081)Success in time 0.166 s
%------------------------------------------------------------------------------
