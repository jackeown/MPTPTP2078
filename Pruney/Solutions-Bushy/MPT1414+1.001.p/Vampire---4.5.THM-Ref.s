%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1414+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:54 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  211 (1450 expanded)
%              Number of leaves         :   22 ( 588 expanded)
%              Depth                    :   55
%              Number of atoms          : 1118 (11890 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21402)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f262,plain,(
    $false ),
    inference(resolution,[],[f261,f58])).

fof(f58,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f51,f50,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
    ( ? [X3] :
        ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r3_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r3_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f261,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f259,f59])).

fof(f59,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f259,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK0)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f257,f104])).

fof(f104,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f103,f62])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_eqrel_1(k8_eqrel_1(X0,sK1),X0)
      | ~ v1_partfun1(sK1,X0) ) ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,X0)
      | m1_eqrel_1(k8_eqrel_1(X0,sK1),X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f80,f61])).

fof(f61,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(f257,plain,(
    ! [X2] :
      ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),X2)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f253,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_eqrel_1)).

fof(f253,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f249,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f249,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f248,f114])).

fof(f114,plain,(
    m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f113,f59])).

fof(f113,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(forward_demodulation,[],[f112,f108])).

fof(f108,plain,(
    k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(resolution,[],[f107,f59])).

fof(f107,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    inference(resolution,[],[f106,f62])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k8_eqrel_1(X0,sK1) = k7_eqrel_1(X0,sK1)
      | ~ v1_partfun1(sK1,X0) ) ),
    inference(resolution,[],[f105,f60])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,X0)
      | k8_eqrel_1(X0,sK1) = k7_eqrel_1(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f81,f61])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(f112,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f111,f62])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v1_partfun1(sK1,X0) ) ),
    inference(resolution,[],[f110,f60])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v3_relat_2(sK1)
      | ~ v1_partfun1(sK1,X0)
      | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f82,f61])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f245,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f244,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f244,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f243,f59])).

fof(f243,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK0)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f241,f104])).

fof(f241,plain,(
    ! [X2] :
      ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),X2)
      | v1_xboole_0(k1_zfmisc_1(sK0))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f235,f67])).

fof(f235,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f234,f132])).

fof(f132,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f66,f129])).

fof(f129,plain,(
    k9_eqrel_1(sK0,sK1,sK2) = k11_relat_1(sK1,sK2) ),
    inference(resolution,[],[f127,f58])).

fof(f127,plain,
    ( v1_xboole_0(sK0)
    | k9_eqrel_1(sK0,sK1,sK2) = k11_relat_1(sK1,sK2) ),
    inference(resolution,[],[f125,f63])).

fof(f63,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_relat_1(sK1,X0) = k9_eqrel_1(sK0,sK1,X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f124,f59])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK1,sK0)
      | k11_relat_1(sK1,X0) = k9_eqrel_1(sK0,sK1,X0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f123,f62])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(sK1,X0)
      | k9_eqrel_1(X0,sK1,X1) = k11_relat_1(sK1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f118,f60])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v3_relat_2(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(sK1,X1)
      | k9_eqrel_1(X1,sK1,X0) = k11_relat_1(sK1,X0)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f84,f61])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_eqrel_1)).

fof(f66,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f234,plain,
    ( r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( v1_xboole_0(sK0)
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f232,f203])).

fof(f203,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f201,f99])).

fof(f99,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f98,f91])).

fof(f91,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f98,plain,
    ( ~ v1_relat_1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f79,f64])).

fof(f64,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
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

fof(f201,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(resolution,[],[f200,f91])).

fof(f200,plain,
    ( ~ v1_relat_1(sK1)
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f198,f92])).

fof(f92,plain,
    ( v1_funct_1(sK3)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f77,f64])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f198,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f196,f93])).

fof(f93,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f78,f64])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_filter_1(X2,X0,X1)
      | v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f196,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f195,f59])).

fof(f195,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
      | m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f194,f62])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_partfun1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f186,f60])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ v3_relat_2(sK1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,sK1),k8_eqrel_1(X1,sK1)),k8_eqrel_1(X1,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_partfun1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f88,f61])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f232,plain,
    ( ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f231,f114])).

fof(f231,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f229,f150])).

fof(f150,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f148,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f148,plain,
    ( m2_subset_1(k11_relat_1(sK1,sK2),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f146,f129])).

fof(f146,plain,
    ( m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f145,f63])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f144,f59])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK1,sK0)
      | m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f143,f62])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(sK1,X0)
      | m2_subset_1(k9_eqrel_1(X0,sK1,X1),k1_zfmisc_1(X0),k8_eqrel_1(X0,sK1))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f142,f60])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v3_relat_2(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(sK1,X1)
      | m2_subset_1(k9_eqrel_1(X1,sK1,X0),k1_zfmisc_1(X1),k8_eqrel_1(X1,sK1))
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f229,plain,
    ( ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f228,f62])).

fof(f228,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f227,f63])).

fof(f227,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f225,f99])).

fof(f225,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f224,f91])).

fof(f224,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f222,f171])).

fof(f171,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f169,f99])).

fof(f169,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f168,f91])).

fof(f168,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f166,f92])).

fof(f166,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f164,f93])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
      | v1_funct_1(k3_filter_1(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f162,f59])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
      | v1_funct_1(k3_filter_1(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f161,f62])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | v1_funct_1(k3_filter_1(X1,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_partfun1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f155,f60])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v3_relat_2(sK1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | v1_funct_1(k3_filter_1(X1,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_partfun1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f86,f61])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f222,plain,
    ( ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f220,f92])).

fof(f220,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f218,f93])).

fof(f218,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(resolution,[],[f217,f59])).

fof(f217,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    inference(resolution,[],[f216,f60])).

fof(f216,plain,
    ( ~ v3_relat_2(sK1)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f215,f61])).

fof(f215,plain,
    ( ~ v8_relat_2(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f213,f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f213,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f212])).

% (21406)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f212,plain,
    ( v1_xboole_0(sK0)
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f183,f193])).

fof(f193,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f192,f129])).

fof(f192,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0)
    | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f191,f65])).

fof(f65,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f190,f91])).

fof(f190,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X0] :
      ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f188,f141])).

fof(f141,plain,(
    ! [X0] :
      ( r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ v1_relat_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f139,f93])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | r1_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f137,f99])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(X0,X0),X0)
      | r1_binop_1(X0,X1,sK3)
      | ~ m1_subset_1(X1,X0)
      | ~ r3_binop_1(X0,X1,sK3)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f126,f91])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(X0,X0),X0)
      | r1_binop_1(X0,X1,sK3)
      | ~ m1_subset_1(X1,X0)
      | ~ r3_binop_1(X0,X1,sK3)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f72,f92])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f188,plain,(
    ! [X0] :
      ( ~ r1_binop_1(sK0,X0,sK3)
      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f187,f64])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m2_filter_1(X0,sK0,sK1)
      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,X0))
      | ~ r1_binop_1(sK0,X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f185,f59])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ m2_filter_1(X1,sK0,sK1)
      | r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ r1_binop_1(sK0,X0,X1)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f184,f62])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X2,X1)
      | ~ m2_filter_1(X0,X1,sK1)
      | r1_binop_1(k8_eqrel_1(X1,sK1),k9_eqrel_1(X1,sK1,X2),k3_filter_1(X1,sK1,X0))
      | ~ r1_binop_1(X1,X2,X0)
      | ~ v1_partfun1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f172,f60])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_relat_2(sK1)
      | ~ m2_filter_1(X2,X0,sK1)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r1_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X1),k3_filter_1(X0,sK1,X2))
      | ~ r1_binop_1(X0,X1,X2)
      | ~ v1_partfun1(sK1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f61])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v8_relat_2(X1)
      | ~ r1_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f183,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    inference(resolution,[],[f182,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_binop_1(X0,X1,X2)
      | r3_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f182,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f181,f129])).

fof(f181,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f180,f65])).

fof(f180,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f178,f158])).

fof(f158,plain,(
    ! [X0] :
      ( r2_binop_1(sK0,X0,sK3)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f157,f91])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | r2_binop_1(sK0,X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( r2_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | ~ v1_relat_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f154,f93])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | r2_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      | r2_binop_1(sK0,X0,sK3)
      | ~ m1_subset_1(X0,sK0)
      | ~ r3_binop_1(sK0,X0,sK3)
      | v1_xboole_0(sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f152,f99])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(X0,X0),X0)
      | r2_binop_1(X0,X1,sK3)
      | ~ m1_subset_1(X1,X0)
      | ~ r3_binop_1(X0,X1,sK3)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f136,f91])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(sK3,k2_zfmisc_1(X0,X0),X0)
      | r2_binop_1(X0,X1,sK3)
      | ~ m1_subset_1(X1,X0)
      | ~ r3_binop_1(X0,X1,sK3)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f73,f92])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | r2_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r2_binop_1(sK0,X0,sK3)
      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,sK3))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f177,f64])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m2_filter_1(X0,sK0,sK1)
      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X1),k3_filter_1(sK0,sK1,X0))
      | ~ r2_binop_1(sK0,X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f176,f59])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK1,sK0)
      | ~ m2_filter_1(X1,sK0,sK1)
      | r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X0),k3_filter_1(sK0,sK1,X1))
      | ~ r2_binop_1(sK0,X0,X1)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f175,f62])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X2,X1)
      | ~ m2_filter_1(X0,X1,sK1)
      | r2_binop_1(k8_eqrel_1(X1,sK1),k9_eqrel_1(X1,sK1,X2),k3_filter_1(X1,sK1,X0))
      | ~ r2_binop_1(X1,X2,X0)
      | ~ v1_partfun1(sK1,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f163,f60])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_relat_2(sK1)
      | ~ m2_filter_1(X2,X0,sK1)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r2_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X1),k3_filter_1(X0,sK1,X2))
      | ~ r2_binop_1(X0,X1,X2)
      | ~ v1_partfun1(sK1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f68,f61])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v8_relat_2(X1)
      | ~ r2_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

%------------------------------------------------------------------------------
