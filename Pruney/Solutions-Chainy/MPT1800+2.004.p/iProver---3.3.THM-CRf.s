%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:02 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :  353 (15637 expanded)
%              Number of clauses        :  264 (4538 expanded)
%              Number of leaves         :   26 (3290 expanded)
%              Depth                    :   45
%              Number of atoms          : 1322 (106866 expanded)
%              Number of equality atoms :  649 (22264 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3)
          | ~ m1_pre_topc(sK3,X0)
          | ~ v1_tsep_1(sK3,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3)
          | ( m1_pre_topc(sK3,X0)
            & v1_tsep_1(sK3,X0) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1)
            | ~ m1_pre_topc(X1,sK2)
            | ~ v1_tsep_1(X1,sK2) )
          & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1)
            | ( m1_pre_topc(X1,sK2)
              & v1_tsep_1(X1,sK2) ) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v1_tsep_1(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
      | ( m1_pre_topc(sK3,sK2)
        & v1_tsep_1(sK3,sK2) ) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f74,f76,f75])).

fof(f120,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f115,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f85,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f107,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f122,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f110,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f65,f66])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f68])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f69,f70])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f123,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f108,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f111,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f125,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_7116,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_7120,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_7123,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_7140,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8524,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7123,c_7140])).

cnf(c_8548,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_8524])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7143,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11890,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8548,c_7143])).

cnf(c_7564,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7565,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7564])).

cnf(c_35,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_7122,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8303,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_7122])).

cnf(c_39284,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11890,c_7565,c_8303,c_8548])).

cnf(c_39285,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_39284])).

cnf(c_39293,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(superposition,[status(thm)],[c_7116,c_39285])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_7136,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_39553,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39293,c_7136])).

cnf(c_50,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_60,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_62,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_69,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_71,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_8194,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8195,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8194])).

cnf(c_8197,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8195])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_7115,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_7130,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9608,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(k8_tmap_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7130,c_7143])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1061,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X1,X0) != X2
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_1062,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1066,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_27])).

cnf(c_1067,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_1068,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_21512,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9608,c_1068])).

cnf(c_21513,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21512])).

cnf(c_21522,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X0)),u1_pre_topc(k8_tmap_1(X0,X0))) = k8_tmap_1(X0,X0)
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_21513])).

cnf(c_27445,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK2)),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7115,c_21522])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7134,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8658,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_7134])).

cnf(c_13152,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8658,c_8548])).

cnf(c_13153,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13152])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_7118,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_39,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_7119,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9712,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7118,c_7119])).

cnf(c_49,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_9854,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9712,c_49,c_50])).

cnf(c_13176,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13153,c_9854])).

cnf(c_7642,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7118,c_7140])).

cnf(c_13396,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13176,c_50,c_7642])).

cnf(c_8549,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7118,c_8524])).

cnf(c_8943,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8549,c_50])).

cnf(c_8948,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8943,c_7143])).

cnf(c_8304,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7118,c_7122])).

cnf(c_9042,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8948,c_50,c_8304])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_7135,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9051,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9042,c_7135])).

cnf(c_9214,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9051])).

cnf(c_12,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7139,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9050,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9042,c_7135])).

cnf(c_9095,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9050])).

cnf(c_9318,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7139,c_9095])).

cnf(c_10192,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9214,c_50,c_7642,c_9318])).

cnf(c_36,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_7121,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10238,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10192,c_7121])).

cnf(c_14245,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13396,c_10238])).

cnf(c_52,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_7917,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_7918,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7917])).

cnf(c_14306,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14245,c_50,c_52,c_7918])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_7124,plain,
    ( u1_struct_0(k6_tmap_1(X0,X1)) = u1_struct_0(X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14317,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14306,c_7124])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_298,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_36,c_29,c_28,c_27])).

cnf(c_299,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_7113,plain,
    ( k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_11453,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7118,c_7113])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_8862,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_11904,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11453,c_47,c_46,c_45,c_43,c_8862])).

cnf(c_14322,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14317,c_11904])).

cnf(c_48,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_14374,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14322,c_48,c_49,c_50])).

cnf(c_14398,plain,
    ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14374,c_7121])).

cnf(c_10158,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_10159,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10158])).

cnf(c_15930,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14398,c_48,c_49,c_50,c_52,c_10159])).

cnf(c_15931,plain,
    ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_15930])).

cnf(c_15938,plain,
    ( m1_pre_topc(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14374,c_15931])).

cnf(c_63,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_65,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_16025,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15938,c_50,c_62,c_65])).

cnf(c_16036,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16025,c_7124])).

cnf(c_61,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_64,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_7607,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))) = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_7609,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7607])).

cnf(c_17872,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16036,c_47,c_46,c_45,c_61,c_64,c_7609])).

cnf(c_11452,plain,
    ( k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_7113])).

cnf(c_17003,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7115,c_11452])).

cnf(c_85,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_88,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_91,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_106,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
    | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_17131,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17003,c_47,c_46,c_45,c_61,c_64,c_85,c_88,c_91,c_106])).

cnf(c_17874,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_17872,c_17131])).

cnf(c_27456,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27445,c_17874])).

cnf(c_27790,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27456,c_48,c_50])).

cnf(c_27865,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27790,c_7135])).

cnf(c_90,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_92,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_17918,plain,
    ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17874,c_7139])).

cnf(c_27866,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27790,c_7135])).

cnf(c_29164,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27865,c_48,c_49,c_50,c_62,c_92,c_17918,c_27866])).

cnf(c_29165,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_29164])).

cnf(c_39566,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_39293,c_29165])).

cnf(c_67,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_70,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_132,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7566,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_7564])).

cnf(c_8196,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8194])).

cnf(c_7862,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X2 = u1_struct_0(X1)
    | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_8232,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_7862])).

cnf(c_9398,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_8232])).

cnf(c_9400,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9398])).

cnf(c_40080,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39566,c_45,c_61,c_67,c_70,c_132,c_7566,c_8196,c_9400])).

cnf(c_40165,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_40080,c_7139])).

cnf(c_40083,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_40080,c_39293])).

cnf(c_40950,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_40083,c_7136])).

cnf(c_42396,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39553,c_50,c_62,c_71,c_8197,c_40165,c_40950])).

cnf(c_42397,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1 ),
    inference(renaming,[status(thm)],[c_42396])).

cnf(c_9862,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7123,c_9854])).

cnf(c_9874,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9862,c_50,c_7642])).

cnf(c_9875,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_9874])).

cnf(c_11454,plain,
    ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9875,c_7113])).

cnf(c_12089,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11454,c_48,c_49,c_50])).

cnf(c_12090,plain,
    ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_12089])).

cnf(c_12098,plain,
    ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_12090])).

cnf(c_12101,plain,
    ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12098,c_10192,c_11904])).

cnf(c_12115,plain,
    ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12101,c_50,c_7642])).

cnf(c_12118,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12115,c_7130])).

cnf(c_12245,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12118,c_48,c_49,c_50,c_52,c_10159])).

cnf(c_12250,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12245,c_7143])).

cnf(c_7581,plain,
    ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v1_pre_topc(k8_tmap_1(X0,X1))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8872,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_7581])).

cnf(c_12029,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_12581,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12250,c_47,c_46,c_45,c_43,c_8872,c_10158,c_12029])).

cnf(c_14378,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_14374,c_12581])).

cnf(c_14841,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
    | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_7136])).

cnf(c_14425,plain,
    ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14374,c_7139])).

cnf(c_21908,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
    | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14841,c_48,c_49,c_50,c_52,c_10159,c_14425])).

cnf(c_21909,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
    inference(renaming,[status(thm)],[c_21908])).

cnf(c_39567,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_39293,c_21909])).

cnf(c_26,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_288,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_36])).

cnf(c_289,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_42,negated_conjecture,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_384,plain,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_42])).

cnf(c_812,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_289,c_384])).

cnf(c_813,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_815,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_45,c_43])).

cnf(c_817,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7141,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14314,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14306,c_7141])).

cnf(c_7578,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7579,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7578])).

cnf(c_16303,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14314,c_50,c_52,c_7579,c_7918])).

cnf(c_16304,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16303])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_7126,plain,
    ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14315,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14306,c_7126])).

cnf(c_7718,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_7722,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7718])).

cnf(c_33093,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14315,c_48,c_49,c_50,c_52,c_7722,c_7918])).

cnf(c_33094,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33093])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_7125,plain,
    ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_14316,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK3))) = k5_tmap_1(sK2,u1_struct_0(sK3))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14306,c_7125])).

cnf(c_14331,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14316,c_11904])).

cnf(c_14832,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14331,c_48,c_49,c_50])).

cnf(c_33097,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33094,c_14832])).

cnf(c_24,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_40,negated_conjecture,
    ( ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_382,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_43,c_40])).

cnf(c_787,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_382])).

cnf(c_788,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_23,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_798,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_382])).

cnf(c_799,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_798])).

cnf(c_800,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_6359,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_6375,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6359])).

cnf(c_6360,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_6376,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6360])).

cnf(c_6353,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6388,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_6353])).

cnf(c_8440,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6353])).

cnf(c_6364,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7629,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X3)
    | X1 != X3
    | X0 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_6364])).

cnf(c_8112,plain,
    ( v3_pre_topc(sK1(X0,X1),X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X3)
    | X2 != X3
    | sK1(X0,X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_7629])).

cnf(c_9665,plain,
    ( v3_pre_topc(sK1(sK2,sK3),X0)
    | ~ v3_pre_topc(u1_struct_0(sK3),X1)
    | X0 != X1
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8112])).

cnf(c_9666,plain,
    ( X0 != X1
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | v3_pre_topc(sK1(sK2,sK3),X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9665])).

cnf(c_9668,plain,
    ( sK1(sK2,sK3) != u1_struct_0(sK3)
    | sK2 != sK2
    | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9666])).

cnf(c_6354,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_7945,plain,
    ( k8_tmap_1(sK2,sK3) != X0
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(X1,X2)
    | g1_pre_topc(X1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_6354])).

cnf(c_8442,plain,
    ( k8_tmap_1(sK2,sK3) != k8_tmap_1(X0,X1)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(X2,X3)
    | g1_pre_topc(X2,X3) != k8_tmap_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_7945])).

cnf(c_11591,plain,
    ( k8_tmap_1(sK2,sK3) != k8_tmap_1(X0,X1)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) != k8_tmap_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_8442])).

cnf(c_15600,plain,
    ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_11591])).

cnf(c_8,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7142,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14313,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14306,c_7142])).

cnf(c_7719,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7720,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7719])).

cnf(c_16296,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14313,c_50,c_52,c_7720,c_7918])).

cnf(c_16297,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16296])).

cnf(c_7576,plain,
    ( k8_tmap_1(sK2,sK3) != X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6354])).

cnf(c_7735,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
    inference(instantiation,[status(thm)],[c_7576])).

cnf(c_12483,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_7735])).

cnf(c_17475,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_12483])).

cnf(c_6361,plain,
    ( X0 != X1
    | X2 != X3
    | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_7773,plain,
    ( X0 != u1_pre_topc(X1)
    | X2 != u1_struct_0(X1)
    | g1_pre_topc(X2,X0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(instantiation,[status(thm)],[c_6361])).

cnf(c_8145,plain,
    ( X0 != u1_struct_0(X1)
    | g1_pre_topc(X0,u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7773])).

cnf(c_8723,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | u1_pre_topc(X1) != u1_pre_topc(X2)
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_8145])).

cnf(c_21806,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | u1_pre_topc(X1) != u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8723])).

cnf(c_21807,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | u1_pre_topc(sK2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_21806])).

cnf(c_7833,plain,
    ( X0 != X1
    | X0 = u1_pre_topc(X2)
    | u1_pre_topc(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_6354])).

cnf(c_8061,plain,
    ( X0 != u1_pre_topc(X1)
    | X0 = u1_pre_topc(X2)
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7833])).

cnf(c_8576,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(X1)
    | u1_pre_topc(X2) != u1_pre_topc(X1)
    | u1_pre_topc(X0) = u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_8061])).

cnf(c_31149,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(X1)
    | u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_8576])).

cnf(c_31150,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_31149])).

cnf(c_7855,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_6354])).

cnf(c_8077,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_7855])).

cnf(c_8614,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_8077])).

cnf(c_31777,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_8614])).

cnf(c_31778,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_31777])).

cnf(c_33101,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33097,c_47,c_48,c_46,c_49,c_45,c_50,c_43,c_52,c_788,c_800,c_6375,c_6376,c_6388,c_8440,c_8872,c_9668,c_10158,c_12029,c_14322,c_15600,c_16297,c_17475,c_21807,c_31150,c_31778])).

cnf(c_31144,plain,
    ( X0 != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6360])).

cnf(c_38671,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_31144])).

cnf(c_41719,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39567,c_47,c_48,c_46,c_49,c_45,c_50,c_43,c_52,c_788,c_800,c_817,c_6375,c_6376,c_6388,c_7579,c_7918,c_8440,c_8872,c_9668,c_10158,c_12029,c_14322,c_15600,c_16297,c_17475,c_21807,c_31150,c_31778,c_33097,c_38671])).

cnf(c_42399,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
    inference(demodulation,[status(thm)],[c_42397,c_41719])).

cnf(c_42405,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(equality_resolution,[status(thm)],[c_42399])).

cnf(c_30,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_7127,plain,
    ( k5_tmap_1(X0,X1) != u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14835,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14832,c_7127])).

cnf(c_17515,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14835,c_48,c_49,c_50,c_52,c_7918])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42405,c_33101,c_17515])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 8.07/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.07/1.49  
% 8.07/1.49  ------  iProver source info
% 8.07/1.49  
% 8.07/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.07/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.07/1.49  git: non_committed_changes: false
% 8.07/1.49  git: last_make_outside_of_git: false
% 8.07/1.49  
% 8.07/1.49  ------ 
% 8.07/1.49  
% 8.07/1.49  ------ Input Options
% 8.07/1.49  
% 8.07/1.49  --out_options                           all
% 8.07/1.49  --tptp_safe_out                         true
% 8.07/1.49  --problem_path                          ""
% 8.07/1.49  --include_path                          ""
% 8.07/1.49  --clausifier                            res/vclausify_rel
% 8.07/1.49  --clausifier_options                    --mode clausify
% 8.07/1.49  --stdin                                 false
% 8.07/1.49  --stats_out                             all
% 8.07/1.49  
% 8.07/1.49  ------ General Options
% 8.07/1.49  
% 8.07/1.49  --fof                                   false
% 8.07/1.49  --time_out_real                         305.
% 8.07/1.49  --time_out_virtual                      -1.
% 8.07/1.49  --symbol_type_check                     false
% 8.07/1.49  --clausify_out                          false
% 8.07/1.49  --sig_cnt_out                           false
% 8.07/1.49  --trig_cnt_out                          false
% 8.07/1.49  --trig_cnt_out_tolerance                1.
% 8.07/1.49  --trig_cnt_out_sk_spl                   false
% 8.07/1.49  --abstr_cl_out                          false
% 8.07/1.49  
% 8.07/1.49  ------ Global Options
% 8.07/1.49  
% 8.07/1.49  --schedule                              default
% 8.07/1.49  --add_important_lit                     false
% 8.07/1.49  --prop_solver_per_cl                    1000
% 8.07/1.49  --min_unsat_core                        false
% 8.07/1.49  --soft_assumptions                      false
% 8.07/1.49  --soft_lemma_size                       3
% 8.07/1.49  --prop_impl_unit_size                   0
% 8.07/1.49  --prop_impl_unit                        []
% 8.07/1.49  --share_sel_clauses                     true
% 8.07/1.49  --reset_solvers                         false
% 8.07/1.49  --bc_imp_inh                            [conj_cone]
% 8.07/1.49  --conj_cone_tolerance                   3.
% 8.07/1.49  --extra_neg_conj                        none
% 8.07/1.49  --large_theory_mode                     true
% 8.07/1.49  --prolific_symb_bound                   200
% 8.07/1.49  --lt_threshold                          2000
% 8.07/1.49  --clause_weak_htbl                      true
% 8.07/1.49  --gc_record_bc_elim                     false
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing Options
% 8.07/1.49  
% 8.07/1.49  --preprocessing_flag                    true
% 8.07/1.49  --time_out_prep_mult                    0.1
% 8.07/1.49  --splitting_mode                        input
% 8.07/1.49  --splitting_grd                         true
% 8.07/1.49  --splitting_cvd                         false
% 8.07/1.49  --splitting_cvd_svl                     false
% 8.07/1.49  --splitting_nvd                         32
% 8.07/1.49  --sub_typing                            true
% 8.07/1.49  --prep_gs_sim                           true
% 8.07/1.49  --prep_unflatten                        true
% 8.07/1.49  --prep_res_sim                          true
% 8.07/1.49  --prep_upred                            true
% 8.07/1.49  --prep_sem_filter                       exhaustive
% 8.07/1.49  --prep_sem_filter_out                   false
% 8.07/1.49  --pred_elim                             true
% 8.07/1.49  --res_sim_input                         true
% 8.07/1.49  --eq_ax_congr_red                       true
% 8.07/1.49  --pure_diseq_elim                       true
% 8.07/1.49  --brand_transform                       false
% 8.07/1.49  --non_eq_to_eq                          false
% 8.07/1.49  --prep_def_merge                        true
% 8.07/1.49  --prep_def_merge_prop_impl              false
% 8.07/1.49  --prep_def_merge_mbd                    true
% 8.07/1.49  --prep_def_merge_tr_red                 false
% 8.07/1.49  --prep_def_merge_tr_cl                  false
% 8.07/1.49  --smt_preprocessing                     true
% 8.07/1.49  --smt_ac_axioms                         fast
% 8.07/1.49  --preprocessed_out                      false
% 8.07/1.49  --preprocessed_stats                    false
% 8.07/1.49  
% 8.07/1.49  ------ Abstraction refinement Options
% 8.07/1.49  
% 8.07/1.49  --abstr_ref                             []
% 8.07/1.49  --abstr_ref_prep                        false
% 8.07/1.49  --abstr_ref_until_sat                   false
% 8.07/1.49  --abstr_ref_sig_restrict                funpre
% 8.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.07/1.49  --abstr_ref_under                       []
% 8.07/1.49  
% 8.07/1.49  ------ SAT Options
% 8.07/1.49  
% 8.07/1.49  --sat_mode                              false
% 8.07/1.49  --sat_fm_restart_options                ""
% 8.07/1.49  --sat_gr_def                            false
% 8.07/1.49  --sat_epr_types                         true
% 8.07/1.49  --sat_non_cyclic_types                  false
% 8.07/1.49  --sat_finite_models                     false
% 8.07/1.49  --sat_fm_lemmas                         false
% 8.07/1.49  --sat_fm_prep                           false
% 8.07/1.49  --sat_fm_uc_incr                        true
% 8.07/1.49  --sat_out_model                         small
% 8.07/1.49  --sat_out_clauses                       false
% 8.07/1.49  
% 8.07/1.49  ------ QBF Options
% 8.07/1.49  
% 8.07/1.49  --qbf_mode                              false
% 8.07/1.49  --qbf_elim_univ                         false
% 8.07/1.49  --qbf_dom_inst                          none
% 8.07/1.49  --qbf_dom_pre_inst                      false
% 8.07/1.49  --qbf_sk_in                             false
% 8.07/1.49  --qbf_pred_elim                         true
% 8.07/1.49  --qbf_split                             512
% 8.07/1.49  
% 8.07/1.49  ------ BMC1 Options
% 8.07/1.49  
% 8.07/1.49  --bmc1_incremental                      false
% 8.07/1.49  --bmc1_axioms                           reachable_all
% 8.07/1.49  --bmc1_min_bound                        0
% 8.07/1.49  --bmc1_max_bound                        -1
% 8.07/1.49  --bmc1_max_bound_default                -1
% 8.07/1.49  --bmc1_symbol_reachability              true
% 8.07/1.49  --bmc1_property_lemmas                  false
% 8.07/1.49  --bmc1_k_induction                      false
% 8.07/1.49  --bmc1_non_equiv_states                 false
% 8.07/1.49  --bmc1_deadlock                         false
% 8.07/1.49  --bmc1_ucm                              false
% 8.07/1.49  --bmc1_add_unsat_core                   none
% 8.07/1.49  --bmc1_unsat_core_children              false
% 8.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.07/1.49  --bmc1_out_stat                         full
% 8.07/1.49  --bmc1_ground_init                      false
% 8.07/1.49  --bmc1_pre_inst_next_state              false
% 8.07/1.49  --bmc1_pre_inst_state                   false
% 8.07/1.49  --bmc1_pre_inst_reach_state             false
% 8.07/1.49  --bmc1_out_unsat_core                   false
% 8.07/1.49  --bmc1_aig_witness_out                  false
% 8.07/1.49  --bmc1_verbose                          false
% 8.07/1.49  --bmc1_dump_clauses_tptp                false
% 8.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.07/1.49  --bmc1_dump_file                        -
% 8.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.07/1.49  --bmc1_ucm_extend_mode                  1
% 8.07/1.49  --bmc1_ucm_init_mode                    2
% 8.07/1.49  --bmc1_ucm_cone_mode                    none
% 8.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.07/1.49  --bmc1_ucm_relax_model                  4
% 8.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.07/1.49  --bmc1_ucm_layered_model                none
% 8.07/1.49  --bmc1_ucm_max_lemma_size               10
% 8.07/1.49  
% 8.07/1.49  ------ AIG Options
% 8.07/1.49  
% 8.07/1.49  --aig_mode                              false
% 8.07/1.49  
% 8.07/1.49  ------ Instantiation Options
% 8.07/1.49  
% 8.07/1.49  --instantiation_flag                    true
% 8.07/1.49  --inst_sos_flag                         false
% 8.07/1.49  --inst_sos_phase                        true
% 8.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel_side                     num_symb
% 8.07/1.49  --inst_solver_per_active                1400
% 8.07/1.49  --inst_solver_calls_frac                1.
% 8.07/1.49  --inst_passive_queue_type               priority_queues
% 8.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.07/1.49  --inst_passive_queues_freq              [25;2]
% 8.07/1.49  --inst_dismatching                      true
% 8.07/1.49  --inst_eager_unprocessed_to_passive     true
% 8.07/1.49  --inst_prop_sim_given                   true
% 8.07/1.49  --inst_prop_sim_new                     false
% 8.07/1.49  --inst_subs_new                         false
% 8.07/1.49  --inst_eq_res_simp                      false
% 8.07/1.49  --inst_subs_given                       false
% 8.07/1.49  --inst_orphan_elimination               true
% 8.07/1.49  --inst_learning_loop_flag               true
% 8.07/1.49  --inst_learning_start                   3000
% 8.07/1.49  --inst_learning_factor                  2
% 8.07/1.49  --inst_start_prop_sim_after_learn       3
% 8.07/1.49  --inst_sel_renew                        solver
% 8.07/1.49  --inst_lit_activity_flag                true
% 8.07/1.49  --inst_restr_to_given                   false
% 8.07/1.49  --inst_activity_threshold               500
% 8.07/1.49  --inst_out_proof                        true
% 8.07/1.49  
% 8.07/1.49  ------ Resolution Options
% 8.07/1.49  
% 8.07/1.49  --resolution_flag                       true
% 8.07/1.49  --res_lit_sel                           adaptive
% 8.07/1.49  --res_lit_sel_side                      none
% 8.07/1.49  --res_ordering                          kbo
% 8.07/1.49  --res_to_prop_solver                    active
% 8.07/1.49  --res_prop_simpl_new                    false
% 8.07/1.49  --res_prop_simpl_given                  true
% 8.07/1.49  --res_passive_queue_type                priority_queues
% 8.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.07/1.49  --res_passive_queues_freq               [15;5]
% 8.07/1.49  --res_forward_subs                      full
% 8.07/1.49  --res_backward_subs                     full
% 8.07/1.49  --res_forward_subs_resolution           true
% 8.07/1.49  --res_backward_subs_resolution          true
% 8.07/1.49  --res_orphan_elimination                true
% 8.07/1.49  --res_time_limit                        2.
% 8.07/1.49  --res_out_proof                         true
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Options
% 8.07/1.49  
% 8.07/1.49  --superposition_flag                    true
% 8.07/1.49  --sup_passive_queue_type                priority_queues
% 8.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.07/1.49  --demod_completeness_check              fast
% 8.07/1.49  --demod_use_ground                      true
% 8.07/1.49  --sup_to_prop_solver                    passive
% 8.07/1.49  --sup_prop_simpl_new                    true
% 8.07/1.49  --sup_prop_simpl_given                  true
% 8.07/1.49  --sup_fun_splitting                     false
% 8.07/1.49  --sup_smt_interval                      50000
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Simplification Setup
% 8.07/1.49  
% 8.07/1.49  --sup_indices_passive                   []
% 8.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_full_bw                           [BwDemod]
% 8.07/1.49  --sup_immed_triv                        [TrivRules]
% 8.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_immed_bw_main                     []
% 8.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  
% 8.07/1.49  ------ Combination Options
% 8.07/1.49  
% 8.07/1.49  --comb_res_mult                         3
% 8.07/1.49  --comb_sup_mult                         2
% 8.07/1.49  --comb_inst_mult                        10
% 8.07/1.49  
% 8.07/1.49  ------ Debug Options
% 8.07/1.49  
% 8.07/1.49  --dbg_backtrace                         false
% 8.07/1.49  --dbg_dump_prop_clauses                 false
% 8.07/1.49  --dbg_dump_prop_clauses_file            -
% 8.07/1.49  --dbg_out_stat                          false
% 8.07/1.49  ------ Parsing...
% 8.07/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.07/1.49  ------ Proving...
% 8.07/1.49  ------ Problem Properties 
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  clauses                                 43
% 8.07/1.49  conjectures                             5
% 8.07/1.49  EPR                                     12
% 8.07/1.49  Horn                                    27
% 8.07/1.49  unary                                   5
% 8.07/1.49  binary                                  7
% 8.07/1.49  lits                                    155
% 8.07/1.49  lits eq                                 21
% 8.07/1.49  fd_pure                                 0
% 8.07/1.49  fd_pseudo                               0
% 8.07/1.49  fd_cond                                 0
% 8.07/1.49  fd_pseudo_cond                          5
% 8.07/1.49  AC symbols                              0
% 8.07/1.49  
% 8.07/1.49  ------ Schedule dynamic 5 is on 
% 8.07/1.49  
% 8.07/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  ------ 
% 8.07/1.49  Current options:
% 8.07/1.49  ------ 
% 8.07/1.49  
% 8.07/1.49  ------ Input Options
% 8.07/1.49  
% 8.07/1.49  --out_options                           all
% 8.07/1.49  --tptp_safe_out                         true
% 8.07/1.49  --problem_path                          ""
% 8.07/1.49  --include_path                          ""
% 8.07/1.49  --clausifier                            res/vclausify_rel
% 8.07/1.49  --clausifier_options                    --mode clausify
% 8.07/1.49  --stdin                                 false
% 8.07/1.49  --stats_out                             all
% 8.07/1.49  
% 8.07/1.49  ------ General Options
% 8.07/1.49  
% 8.07/1.49  --fof                                   false
% 8.07/1.49  --time_out_real                         305.
% 8.07/1.49  --time_out_virtual                      -1.
% 8.07/1.49  --symbol_type_check                     false
% 8.07/1.49  --clausify_out                          false
% 8.07/1.49  --sig_cnt_out                           false
% 8.07/1.49  --trig_cnt_out                          false
% 8.07/1.49  --trig_cnt_out_tolerance                1.
% 8.07/1.49  --trig_cnt_out_sk_spl                   false
% 8.07/1.49  --abstr_cl_out                          false
% 8.07/1.49  
% 8.07/1.49  ------ Global Options
% 8.07/1.49  
% 8.07/1.49  --schedule                              default
% 8.07/1.49  --add_important_lit                     false
% 8.07/1.49  --prop_solver_per_cl                    1000
% 8.07/1.49  --min_unsat_core                        false
% 8.07/1.49  --soft_assumptions                      false
% 8.07/1.49  --soft_lemma_size                       3
% 8.07/1.49  --prop_impl_unit_size                   0
% 8.07/1.49  --prop_impl_unit                        []
% 8.07/1.49  --share_sel_clauses                     true
% 8.07/1.49  --reset_solvers                         false
% 8.07/1.49  --bc_imp_inh                            [conj_cone]
% 8.07/1.49  --conj_cone_tolerance                   3.
% 8.07/1.49  --extra_neg_conj                        none
% 8.07/1.49  --large_theory_mode                     true
% 8.07/1.49  --prolific_symb_bound                   200
% 8.07/1.49  --lt_threshold                          2000
% 8.07/1.49  --clause_weak_htbl                      true
% 8.07/1.49  --gc_record_bc_elim                     false
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing Options
% 8.07/1.49  
% 8.07/1.49  --preprocessing_flag                    true
% 8.07/1.49  --time_out_prep_mult                    0.1
% 8.07/1.49  --splitting_mode                        input
% 8.07/1.49  --splitting_grd                         true
% 8.07/1.49  --splitting_cvd                         false
% 8.07/1.49  --splitting_cvd_svl                     false
% 8.07/1.49  --splitting_nvd                         32
% 8.07/1.49  --sub_typing                            true
% 8.07/1.49  --prep_gs_sim                           true
% 8.07/1.49  --prep_unflatten                        true
% 8.07/1.49  --prep_res_sim                          true
% 8.07/1.49  --prep_upred                            true
% 8.07/1.49  --prep_sem_filter                       exhaustive
% 8.07/1.49  --prep_sem_filter_out                   false
% 8.07/1.49  --pred_elim                             true
% 8.07/1.49  --res_sim_input                         true
% 8.07/1.49  --eq_ax_congr_red                       true
% 8.07/1.49  --pure_diseq_elim                       true
% 8.07/1.49  --brand_transform                       false
% 8.07/1.49  --non_eq_to_eq                          false
% 8.07/1.49  --prep_def_merge                        true
% 8.07/1.49  --prep_def_merge_prop_impl              false
% 8.07/1.49  --prep_def_merge_mbd                    true
% 8.07/1.49  --prep_def_merge_tr_red                 false
% 8.07/1.49  --prep_def_merge_tr_cl                  false
% 8.07/1.49  --smt_preprocessing                     true
% 8.07/1.49  --smt_ac_axioms                         fast
% 8.07/1.49  --preprocessed_out                      false
% 8.07/1.49  --preprocessed_stats                    false
% 8.07/1.49  
% 8.07/1.49  ------ Abstraction refinement Options
% 8.07/1.49  
% 8.07/1.49  --abstr_ref                             []
% 8.07/1.49  --abstr_ref_prep                        false
% 8.07/1.49  --abstr_ref_until_sat                   false
% 8.07/1.49  --abstr_ref_sig_restrict                funpre
% 8.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.07/1.49  --abstr_ref_under                       []
% 8.07/1.49  
% 8.07/1.49  ------ SAT Options
% 8.07/1.49  
% 8.07/1.49  --sat_mode                              false
% 8.07/1.49  --sat_fm_restart_options                ""
% 8.07/1.49  --sat_gr_def                            false
% 8.07/1.49  --sat_epr_types                         true
% 8.07/1.49  --sat_non_cyclic_types                  false
% 8.07/1.49  --sat_finite_models                     false
% 8.07/1.49  --sat_fm_lemmas                         false
% 8.07/1.49  --sat_fm_prep                           false
% 8.07/1.49  --sat_fm_uc_incr                        true
% 8.07/1.49  --sat_out_model                         small
% 8.07/1.49  --sat_out_clauses                       false
% 8.07/1.49  
% 8.07/1.49  ------ QBF Options
% 8.07/1.49  
% 8.07/1.49  --qbf_mode                              false
% 8.07/1.49  --qbf_elim_univ                         false
% 8.07/1.49  --qbf_dom_inst                          none
% 8.07/1.49  --qbf_dom_pre_inst                      false
% 8.07/1.49  --qbf_sk_in                             false
% 8.07/1.49  --qbf_pred_elim                         true
% 8.07/1.49  --qbf_split                             512
% 8.07/1.49  
% 8.07/1.49  ------ BMC1 Options
% 8.07/1.49  
% 8.07/1.49  --bmc1_incremental                      false
% 8.07/1.49  --bmc1_axioms                           reachable_all
% 8.07/1.49  --bmc1_min_bound                        0
% 8.07/1.49  --bmc1_max_bound                        -1
% 8.07/1.49  --bmc1_max_bound_default                -1
% 8.07/1.49  --bmc1_symbol_reachability              true
% 8.07/1.49  --bmc1_property_lemmas                  false
% 8.07/1.49  --bmc1_k_induction                      false
% 8.07/1.49  --bmc1_non_equiv_states                 false
% 8.07/1.49  --bmc1_deadlock                         false
% 8.07/1.49  --bmc1_ucm                              false
% 8.07/1.49  --bmc1_add_unsat_core                   none
% 8.07/1.49  --bmc1_unsat_core_children              false
% 8.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.07/1.49  --bmc1_out_stat                         full
% 8.07/1.49  --bmc1_ground_init                      false
% 8.07/1.49  --bmc1_pre_inst_next_state              false
% 8.07/1.49  --bmc1_pre_inst_state                   false
% 8.07/1.49  --bmc1_pre_inst_reach_state             false
% 8.07/1.49  --bmc1_out_unsat_core                   false
% 8.07/1.49  --bmc1_aig_witness_out                  false
% 8.07/1.49  --bmc1_verbose                          false
% 8.07/1.49  --bmc1_dump_clauses_tptp                false
% 8.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.07/1.49  --bmc1_dump_file                        -
% 8.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.07/1.49  --bmc1_ucm_extend_mode                  1
% 8.07/1.49  --bmc1_ucm_init_mode                    2
% 8.07/1.49  --bmc1_ucm_cone_mode                    none
% 8.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.07/1.49  --bmc1_ucm_relax_model                  4
% 8.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.07/1.49  --bmc1_ucm_layered_model                none
% 8.07/1.49  --bmc1_ucm_max_lemma_size               10
% 8.07/1.49  
% 8.07/1.49  ------ AIG Options
% 8.07/1.49  
% 8.07/1.49  --aig_mode                              false
% 8.07/1.49  
% 8.07/1.49  ------ Instantiation Options
% 8.07/1.49  
% 8.07/1.49  --instantiation_flag                    true
% 8.07/1.49  --inst_sos_flag                         false
% 8.07/1.49  --inst_sos_phase                        true
% 8.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel_side                     none
% 8.07/1.49  --inst_solver_per_active                1400
% 8.07/1.49  --inst_solver_calls_frac                1.
% 8.07/1.49  --inst_passive_queue_type               priority_queues
% 8.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.07/1.49  --inst_passive_queues_freq              [25;2]
% 8.07/1.49  --inst_dismatching                      true
% 8.07/1.49  --inst_eager_unprocessed_to_passive     true
% 8.07/1.49  --inst_prop_sim_given                   true
% 8.07/1.49  --inst_prop_sim_new                     false
% 8.07/1.49  --inst_subs_new                         false
% 8.07/1.49  --inst_eq_res_simp                      false
% 8.07/1.49  --inst_subs_given                       false
% 8.07/1.49  --inst_orphan_elimination               true
% 8.07/1.49  --inst_learning_loop_flag               true
% 8.07/1.49  --inst_learning_start                   3000
% 8.07/1.49  --inst_learning_factor                  2
% 8.07/1.49  --inst_start_prop_sim_after_learn       3
% 8.07/1.49  --inst_sel_renew                        solver
% 8.07/1.49  --inst_lit_activity_flag                true
% 8.07/1.49  --inst_restr_to_given                   false
% 8.07/1.49  --inst_activity_threshold               500
% 8.07/1.49  --inst_out_proof                        true
% 8.07/1.49  
% 8.07/1.49  ------ Resolution Options
% 8.07/1.49  
% 8.07/1.49  --resolution_flag                       false
% 8.07/1.49  --res_lit_sel                           adaptive
% 8.07/1.49  --res_lit_sel_side                      none
% 8.07/1.49  --res_ordering                          kbo
% 8.07/1.49  --res_to_prop_solver                    active
% 8.07/1.49  --res_prop_simpl_new                    false
% 8.07/1.49  --res_prop_simpl_given                  true
% 8.07/1.49  --res_passive_queue_type                priority_queues
% 8.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.07/1.49  --res_passive_queues_freq               [15;5]
% 8.07/1.49  --res_forward_subs                      full
% 8.07/1.49  --res_backward_subs                     full
% 8.07/1.49  --res_forward_subs_resolution           true
% 8.07/1.49  --res_backward_subs_resolution          true
% 8.07/1.49  --res_orphan_elimination                true
% 8.07/1.49  --res_time_limit                        2.
% 8.07/1.49  --res_out_proof                         true
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Options
% 8.07/1.49  
% 8.07/1.49  --superposition_flag                    true
% 8.07/1.49  --sup_passive_queue_type                priority_queues
% 8.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.07/1.49  --demod_completeness_check              fast
% 8.07/1.49  --demod_use_ground                      true
% 8.07/1.49  --sup_to_prop_solver                    passive
% 8.07/1.49  --sup_prop_simpl_new                    true
% 8.07/1.49  --sup_prop_simpl_given                  true
% 8.07/1.49  --sup_fun_splitting                     false
% 8.07/1.49  --sup_smt_interval                      50000
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Simplification Setup
% 8.07/1.49  
% 8.07/1.49  --sup_indices_passive                   []
% 8.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_full_bw                           [BwDemod]
% 8.07/1.49  --sup_immed_triv                        [TrivRules]
% 8.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_immed_bw_main                     []
% 8.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  
% 8.07/1.49  ------ Combination Options
% 8.07/1.49  
% 8.07/1.49  --comb_res_mult                         3
% 8.07/1.49  --comb_sup_mult                         2
% 8.07/1.49  --comb_inst_mult                        10
% 8.07/1.49  
% 8.07/1.49  ------ Debug Options
% 8.07/1.49  
% 8.07/1.49  --dbg_backtrace                         false
% 8.07/1.49  --dbg_dump_prop_clauses                 false
% 8.07/1.49  --dbg_dump_prop_clauses_file            -
% 8.07/1.49  --dbg_out_stat                          false
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  ------ Proving...
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  % SZS status Theorem for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  fof(f24,conjecture,(
% 8.07/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f25,negated_conjecture,(
% 8.07/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 8.07/1.49    inference(negated_conjecture,[],[f24])).
% 8.07/1.49  
% 8.07/1.49  fof(f60,plain,(
% 8.07/1.49    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.07/1.49    inference(ennf_transformation,[],[f25])).
% 8.07/1.49  
% 8.07/1.49  fof(f61,plain,(
% 8.07/1.49    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.07/1.50    inference(flattening,[],[f60])).
% 8.07/1.50  
% 8.07/1.50  fof(f73,plain,(
% 8.07/1.50    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.07/1.50    inference(nnf_transformation,[],[f61])).
% 8.07/1.50  
% 8.07/1.50  fof(f74,plain,(
% 8.07/1.50    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.07/1.50    inference(flattening,[],[f73])).
% 8.07/1.50  
% 8.07/1.50  fof(f76,plain,(
% 8.07/1.50    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(sK3,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3) | (m1_pre_topc(sK3,X0) & v1_tsep_1(sK3,X0))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 8.07/1.50    introduced(choice_axiom,[])).
% 8.07/1.50  
% 8.07/1.50  fof(f75,plain,(
% 8.07/1.50    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1) | ~m1_pre_topc(X1,sK2) | ~v1_tsep_1(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1) | (m1_pre_topc(X1,sK2) & v1_tsep_1(X1,sK2))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 8.07/1.50    introduced(choice_axiom,[])).
% 8.07/1.50  
% 8.07/1.50  fof(f77,plain,(
% 8.07/1.50    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | (m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 8.07/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f74,f76,f75])).
% 8.07/1.50  
% 8.07/1.50  fof(f120,plain,(
% 8.07/1.50    l1_pre_topc(sK2)),
% 8.07/1.50    inference(cnf_transformation,[],[f77])).
% 8.07/1.50  
% 8.07/1.50  fof(f21,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f56,plain,(
% 8.07/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f21])).
% 8.07/1.50  
% 8.07/1.50  fof(f115,plain,(
% 8.07/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f56])).
% 8.07/1.50  
% 8.07/1.50  fof(f19,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f54,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f19])).
% 8.07/1.50  
% 8.07/1.50  fof(f113,plain,(
% 8.07/1.50    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f54])).
% 8.07/1.50  
% 8.07/1.50  fof(f8,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f36,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f8])).
% 8.07/1.50  
% 8.07/1.50  fof(f89,plain,(
% 8.07/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f36])).
% 8.07/1.50  
% 8.07/1.50  fof(f5,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f32,plain,(
% 8.07/1.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f5])).
% 8.07/1.50  
% 8.07/1.50  fof(f33,plain,(
% 8.07/1.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(flattening,[],[f32])).
% 8.07/1.50  
% 8.07/1.50  fof(f85,plain,(
% 8.07/1.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f33])).
% 8.07/1.50  
% 8.07/1.50  fof(f112,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f54])).
% 8.07/1.50  
% 8.07/1.50  fof(f12,axiom,(
% 8.07/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f42,plain,(
% 8.07/1.50    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.07/1.50    inference(ennf_transformation,[],[f12])).
% 8.07/1.50  
% 8.07/1.50  fof(f95,plain,(
% 8.07/1.50    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.07/1.50    inference(cnf_transformation,[],[f42])).
% 8.07/1.50  
% 8.07/1.50  fof(f119,plain,(
% 8.07/1.50    v2_pre_topc(sK2)),
% 8.07/1.50    inference(cnf_transformation,[],[f77])).
% 8.07/1.50  
% 8.07/1.50  fof(f16,axiom,(
% 8.07/1.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f48,plain,(
% 8.07/1.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.07/1.50    inference(ennf_transformation,[],[f16])).
% 8.07/1.50  
% 8.07/1.50  fof(f49,plain,(
% 8.07/1.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(flattening,[],[f48])).
% 8.07/1.50  
% 8.07/1.50  fof(f107,plain,(
% 8.07/1.50    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f49])).
% 8.07/1.50  
% 8.07/1.50  fof(f105,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f49])).
% 8.07/1.50  
% 8.07/1.50  fof(f13,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f43,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f13])).
% 8.07/1.50  
% 8.07/1.50  fof(f96,plain,(
% 8.07/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f43])).
% 8.07/1.50  
% 8.07/1.50  fof(f122,plain,(
% 8.07/1.50    m1_pre_topc(sK3,sK2)),
% 8.07/1.50    inference(cnf_transformation,[],[f77])).
% 8.07/1.50  
% 8.07/1.50  fof(f23,axiom,(
% 8.07/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f58,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.07/1.50    inference(ennf_transformation,[],[f23])).
% 8.07/1.50  
% 8.07/1.50  fof(f59,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.07/1.50    inference(flattening,[],[f58])).
% 8.07/1.50  
% 8.07/1.50  fof(f117,plain,(
% 8.07/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f59])).
% 8.07/1.50  
% 8.07/1.50  fof(f94,plain,(
% 8.07/1.50    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.07/1.50    inference(cnf_transformation,[],[f42])).
% 8.07/1.50  
% 8.07/1.50  fof(f9,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f37,plain,(
% 8.07/1.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f9])).
% 8.07/1.50  
% 8.07/1.50  fof(f90,plain,(
% 8.07/1.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f37])).
% 8.07/1.50  
% 8.07/1.50  fof(f20,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f55,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f20])).
% 8.07/1.50  
% 8.07/1.50  fof(f114,plain,(
% 8.07/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f55])).
% 8.07/1.50  
% 8.07/1.50  fof(f18,axiom,(
% 8.07/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f52,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.07/1.50    inference(ennf_transformation,[],[f18])).
% 8.07/1.50  
% 8.07/1.50  fof(f53,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(flattening,[],[f52])).
% 8.07/1.50  
% 8.07/1.50  fof(f110,plain,(
% 8.07/1.50    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f53])).
% 8.07/1.50  
% 8.07/1.50  fof(f14,axiom,(
% 8.07/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f44,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.07/1.50    inference(ennf_transformation,[],[f14])).
% 8.07/1.50  
% 8.07/1.50  fof(f45,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(flattening,[],[f44])).
% 8.07/1.50  
% 8.07/1.50  fof(f64,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(nnf_transformation,[],[f45])).
% 8.07/1.50  
% 8.07/1.50  fof(f65,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(rectify,[],[f64])).
% 8.07/1.50  
% 8.07/1.50  fof(f66,plain,(
% 8.07/1.50    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.07/1.50    introduced(choice_axiom,[])).
% 8.07/1.50  
% 8.07/1.50  fof(f67,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f65,f66])).
% 8.07/1.50  
% 8.07/1.50  fof(f97,plain,(
% 8.07/1.50    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f67])).
% 8.07/1.50  
% 8.07/1.50  fof(f126,plain,(
% 8.07/1.50    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(equality_resolution,[],[f97])).
% 8.07/1.50  
% 8.07/1.50  fof(f127,plain,(
% 8.07/1.50    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(equality_resolution,[],[f126])).
% 8.07/1.50  
% 8.07/1.50  fof(f106,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f49])).
% 8.07/1.50  
% 8.07/1.50  fof(f118,plain,(
% 8.07/1.50    ~v2_struct_0(sK2)),
% 8.07/1.50    inference(cnf_transformation,[],[f77])).
% 8.07/1.50  
% 8.07/1.50  fof(f15,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f46,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f15])).
% 8.07/1.50  
% 8.07/1.50  fof(f47,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(flattening,[],[f46])).
% 8.07/1.50  
% 8.07/1.50  fof(f68,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(nnf_transformation,[],[f47])).
% 8.07/1.50  
% 8.07/1.50  fof(f69,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(rectify,[],[f68])).
% 8.07/1.50  
% 8.07/1.50  fof(f70,plain,(
% 8.07/1.50    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.07/1.50    introduced(choice_axiom,[])).
% 8.07/1.50  
% 8.07/1.50  fof(f71,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f69,f70])).
% 8.07/1.50  
% 8.07/1.50  fof(f101,plain,(
% 8.07/1.50    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f71])).
% 8.07/1.50  
% 8.07/1.50  fof(f128,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(equality_resolution,[],[f101])).
% 8.07/1.50  
% 8.07/1.50  fof(f123,plain,(
% 8.07/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | v1_tsep_1(sK3,sK2)),
% 8.07/1.50    inference(cnf_transformation,[],[f77])).
% 8.07/1.50  
% 8.07/1.50  fof(f6,axiom,(
% 8.07/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f34,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(ennf_transformation,[],[f6])).
% 8.07/1.50  
% 8.07/1.50  fof(f63,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.07/1.50    inference(nnf_transformation,[],[f34])).
% 8.07/1.50  
% 8.07/1.50  fof(f86,plain,(
% 8.07/1.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f63])).
% 8.07/1.50  
% 8.07/1.50  fof(f17,axiom,(
% 8.07/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 8.07/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.50  
% 8.07/1.50  fof(f50,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.07/1.50    inference(ennf_transformation,[],[f17])).
% 8.07/1.50  
% 8.07/1.50  fof(f51,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(flattening,[],[f50])).
% 8.07/1.50  
% 8.07/1.50  fof(f72,plain,(
% 8.07/1.50    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.07/1.50    inference(nnf_transformation,[],[f51])).
% 8.07/1.50  
% 8.07/1.50  fof(f108,plain,(
% 8.07/1.50    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f72])).
% 8.07/1.50  
% 8.07/1.50  fof(f111,plain,(
% 8.07/1.50    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f53])).
% 8.07/1.50  
% 8.07/1.50  fof(f103,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f71])).
% 8.07/1.50  
% 8.07/1.50  fof(f125,plain,(
% 8.07/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)),
% 8.07/1.50    inference(cnf_transformation,[],[f77])).
% 8.07/1.50  
% 8.07/1.50  fof(f104,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f71])).
% 8.07/1.50  
% 8.07/1.50  fof(f87,plain,(
% 8.07/1.50    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f63])).
% 8.07/1.50  
% 8.07/1.50  fof(f109,plain,(
% 8.07/1.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.07/1.50    inference(cnf_transformation,[],[f72])).
% 8.07/1.50  
% 8.07/1.50  cnf(c_45,negated_conjecture,
% 8.07/1.50      ( l1_pre_topc(sK2) ),
% 8.07/1.50      inference(cnf_transformation,[],[f120]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7116,plain,
% 8.07/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_37,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f115]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7120,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_34,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f113]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7123,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f89]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7140,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(X0) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8524,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7123,c_7140]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8548,plain,
% 8.07/1.50      ( l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7120,c_8524]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7,plain,
% 8.07/1.50      ( ~ l1_pre_topc(X0)
% 8.07/1.50      | ~ v1_pre_topc(X0)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 8.07/1.50      inference(cnf_transformation,[],[f85]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7143,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | v1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11890,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_8548,c_7143]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7564,plain,
% 8.07/1.50      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 8.07/1.50      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7565,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_7564]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_35,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 8.07/1.50      inference(cnf_transformation,[],[f112]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7122,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8303,plain,
% 8.07/1.50      ( l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7120,c_7122]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39284,plain,
% 8.07/1.50      ( l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_11890,c_7565,c_8303,c_8548]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39285,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_39284]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39293,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7116,c_39285]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16,plain,
% 8.07/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.07/1.50      | X2 = X0
% 8.07/1.50      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f95]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7136,plain,
% 8.07/1.50      ( X0 = X1
% 8.07/1.50      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39553,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 8.07/1.50      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_39293,c_7136]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_50,plain,
% 8.07/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_60,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_62,plain,
% 8.07/1.50      ( m1_pre_topc(sK2,sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_60]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_69,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_71,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) = iProver_top
% 8.07/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_69]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8194,plain,
% 8.07/1.50      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8195,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_8194]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8197,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8195]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_46,negated_conjecture,
% 8.07/1.50      ( v2_pre_topc(sK2) ),
% 8.07/1.50      inference(cnf_transformation,[],[f119]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7115,plain,
% 8.07/1.50      ( v2_pre_topc(sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 8.07/1.50      inference(cnf_transformation,[],[f107]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7130,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | v2_pre_topc(X1) != iProver_top
% 8.07/1.50      | v2_struct_0(X1) = iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9608,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1)
% 8.07/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | v1_pre_topc(k8_tmap_1(X0,X1)) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7130,c_7143]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_29,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 8.07/1.50      inference(cnf_transformation,[],[f105]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1061,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | ~ l1_pre_topc(X2)
% 8.07/1.50      | k8_tmap_1(X1,X0) != X2
% 8.07/1.50      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X2 ),
% 8.07/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1062,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
% 8.07/1.50      inference(unflattening,[status(thm)],[c_1061]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1066,plain,
% 8.07/1.50      ( ~ l1_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_1062,c_27]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1067,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_1066]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1068,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1)
% 8.07/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21512,plain,
% 8.07/1.50      ( l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_9608,c_1068]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21513,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1)
% 8.07/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_21512]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21522,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X0)),u1_pre_topc(k8_tmap_1(X0,X0))) = k8_tmap_1(X0,X0)
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7120,c_21513]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27445,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK2)),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2)
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7115,c_21522]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_18,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f96]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7134,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 8.07/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8658,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7120,c_7134]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_13152,plain,
% 8.07/1.50      ( l1_pre_topc(X0) != iProver_top
% 8.07/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_8658,c_8548]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_13153,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_13152]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_43,negated_conjecture,
% 8.07/1.50      ( m1_pre_topc(sK3,sK2) ),
% 8.07/1.50      inference(cnf_transformation,[],[f122]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7118,plain,
% 8.07/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ m1_pre_topc(X2,X0)
% 8.07/1.50      | m1_pre_topc(X2,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f117]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7119,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 8.07/1.50      | m1_pre_topc(X2,X1) = iProver_top
% 8.07/1.50      | v2_pre_topc(X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9712,plain,
% 8.07/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 8.07/1.50      | m1_pre_topc(X0,sK2) = iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7118,c_7119]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_49,plain,
% 8.07/1.50      ( v2_pre_topc(sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9854,plain,
% 8.07/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 8.07/1.50      | m1_pre_topc(X0,sK2) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_9712,c_49,c_50]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_13176,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_13153,c_9854]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7642,plain,
% 8.07/1.50      ( l1_pre_topc(sK3) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7118,c_7140]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_13396,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_13176,c_50,c_7642]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8549,plain,
% 8.07/1.50      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7118,c_8524]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8943,plain,
% 8.07/1.50      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_8549,c_50]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8948,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_8943,c_7143]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8304,plain,
% 8.07/1.50      ( l1_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7118,c_7122]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9042,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_8948,c_50,c_8304]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17,plain,
% 8.07/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.07/1.50      | X2 = X1
% 8.07/1.50      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f94]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7135,plain,
% 8.07/1.50      ( X0 = X1
% 8.07/1.50      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 8.07/1.50      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9051,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 8.07/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
% 8.07/1.50      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_9042,c_7135]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9214,plain,
% 8.07/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 8.07/1.50      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 8.07/1.50      inference(equality_resolution,[status(thm)],[c_9051]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12,plain,
% 8.07/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.07/1.50      | ~ l1_pre_topc(X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f90]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7139,plain,
% 8.07/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9050,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 8.07/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_9042,c_7135]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9095,plain,
% 8.07/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 8.07/1.50      | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 8.07/1.50      inference(equality_resolution,[status(thm)],[c_9050]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9318,plain,
% 8.07/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 8.07/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7139,c_9095]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_10192,plain,
% 8.07/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_9214,c_50,c_7642,c_9318]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_36,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f114]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7121,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_10238,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_10192,c_7121]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14245,plain,
% 8.07/1.50      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_13396,c_10238]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_52,plain,
% 8.07/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7917,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_36]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7918,plain,
% 8.07/1.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_7917]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14306,plain,
% 8.07/1.50      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14245,c_50,c_52,c_7918]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_33,plain,
% 8.07/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f110]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7124,plain,
% 8.07/1.50      ( u1_struct_0(k6_tmap_1(X0,X1)) = u1_struct_0(X0)
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14317,plain,
% 8.07/1.50      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2)
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14306,c_7124]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_22,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 8.07/1.50      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 8.07/1.50      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f127]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_28,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_pre_topc(k8_tmap_1(X1,X0))
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f106]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_298,plain,
% 8.07/1.50      ( ~ v2_pre_topc(X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_22,c_36,c_29,c_28,c_27]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_299,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_298]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7113,plain,
% 8.07/1.50      ( k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 8.07/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11453,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7118,c_7113]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_47,negated_conjecture,
% 8.07/1.50      ( ~ v2_struct_0(sK2) ),
% 8.07/1.50      inference(cnf_transformation,[],[f118]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8862,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_299]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11904,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_11453,c_47,c_46,c_45,c_43,c_8862]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14322,plain,
% 8.07/1.50      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(light_normalisation,[status(thm)],[c_14317,c_11904]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_48,plain,
% 8.07/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14374,plain,
% 8.07/1.50      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14322,c_48,c_49,c_50]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14398,plain,
% 8.07/1.50      ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14374,c_7121]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_10158,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_27]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_10159,plain,
% 8.07/1.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_10158]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_15930,plain,
% 8.07/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.07/1.50      | m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14398,c_48,c_49,c_50,c_52,c_10159]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_15931,plain,
% 8.07/1.50      ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_15930]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_15938,plain,
% 8.07/1.50      ( m1_pre_topc(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3)) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14374,c_15931]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_63,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_65,plain,
% 8.07/1.50      ( m1_pre_topc(sK2,sK2) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_63]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16025,plain,
% 8.07/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_15938,c_50,c_62,c_65]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16036,plain,
% 8.07/1.50      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2)
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_16025,c_7124]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_61,plain,
% 8.07/1.50      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_64,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_36]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7607,plain,
% 8.07/1.50      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))) = u1_struct_0(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_33]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7609,plain,
% 8.07/1.50      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7607]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17872,plain,
% 8.07/1.50      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_16036,c_47,c_46,c_45,c_61,c_64,c_7609]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11452,plain,
% 8.07/1.50      ( k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7120,c_7113]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17003,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2)
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7115,c_11452]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_85,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | v1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_88,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | v2_pre_topc(k8_tmap_1(sK2,sK2))
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_28]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_91,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK2))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_27]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_106,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
% 8.07/1.50      | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_22]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17131,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_17003,c_47,c_46,c_45,c_61,c_64,c_85,c_88,c_91,c_106]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17874,plain,
% 8.07/1.50      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(light_normalisation,[status(thm)],[c_17872,c_17131]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27456,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2)
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(light_normalisation,[status(thm)],[c_27445,c_17874]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27790,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_27456,c_48,c_50]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27865,plain,
% 8.07/1.50      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
% 8.07/1.50      | u1_struct_0(sK2) = X0
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_27790,c_7135]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_90,plain,
% 8.07/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | v2_pre_topc(X1) != iProver_top
% 8.07/1.50      | v2_struct_0(X1) = iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_92,plain,
% 8.07/1.50      ( m1_pre_topc(sK2,sK2) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_90]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17918,plain,
% 8.07/1.50      ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK2)) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_17874,c_7139]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27866,plain,
% 8.07/1.50      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
% 8.07/1.50      | u1_struct_0(sK2) = X0
% 8.07/1.50      | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_27790,c_7135]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_29164,plain,
% 8.07/1.50      ( u1_struct_0(sK2) = X0
% 8.07/1.50      | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_27865,c_48,c_49,c_50,c_62,c_92,c_17918,c_27866]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_29165,plain,
% 8.07/1.50      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
% 8.07/1.50      | u1_struct_0(sK2) = X0 ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_29164]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39566,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK2)
% 8.07/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_39293,c_29165]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_67,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_35]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_70,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 8.07/1.50      | ~ m1_pre_topc(sK2,sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_34]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_132,plain,
% 8.07/1.50      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7566,plain,
% 8.07/1.50      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 8.07/1.50      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7564]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8196,plain,
% 8.07/1.50      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8194]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7862,plain,
% 8.07/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.07/1.50      | X2 = u1_struct_0(X1)
% 8.07/1.50      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8232,plain,
% 8.07/1.50      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.07/1.50      | X1 = u1_struct_0(X0)
% 8.07/1.50      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7862]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9398,plain,
% 8.07/1.50      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.07/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8232]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9400,plain,
% 8.07/1.50      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 8.07/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_9398]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_40080,plain,
% 8.07/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_39566,c_45,c_61,c_67,c_70,c_132,c_7566,c_8196,c_9400]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_40165,plain,
% 8.07/1.50      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.07/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_40080,c_7139]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_40083,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 8.07/1.50      inference(demodulation,[status(thm)],[c_40080,c_39293]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_40950,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 8.07/1.50      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
% 8.07/1.50      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_40083,c_7136]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_42396,plain,
% 8.07/1.50      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_39553,c_50,c_62,c_71,c_8197,c_40165,c_40950]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_42397,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 8.07/1.50      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1 ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_42396]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9862,plain,
% 8.07/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 8.07/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7123,c_9854]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9874,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
% 8.07/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_9862,c_50,c_7642]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9875,plain,
% 8.07/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 8.07/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_9874]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11454,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 8.07/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_9875,c_7113]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12089,plain,
% 8.07/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 8.07/1.50      | k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_11454,c_48,c_49,c_50]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12090,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 8.07/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_12089]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12098,plain,
% 8.07/1.50      ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 8.07/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_7120,c_12090]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12101,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 8.07/1.50      inference(light_normalisation,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_12098,c_10192,c_11904]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12115,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_12101,c_50,c_7642]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12118,plain,
% 8.07/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_12115,c_7130]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12245,plain,
% 8.07/1.50      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_12118,c_48,c_49,c_50,c_52,c_10159]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12250,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_12245,c_7143]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7581,plain,
% 8.07/1.50      ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
% 8.07/1.50      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8872,plain,
% 8.07/1.50      ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7581]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12029,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12581,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_12250,c_47,c_46,c_45,c_43,c_8872,c_10158,c_12029]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14378,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(demodulation,[status(thm)],[c_14374,c_12581]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14841,plain,
% 8.07/1.50      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
% 8.07/1.50      | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14378,c_7136]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14425,plain,
% 8.07/1.50      ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.07/1.50      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14374,c_7139]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21908,plain,
% 8.07/1.50      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
% 8.07/1.50      | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14841,c_48,c_49,c_50,c_52,c_10159,c_14425]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21909,plain,
% 8.07/1.50      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_21908]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_39567,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_39293,c_21909]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_26,plain,
% 8.07/1.50      ( ~ v1_tsep_1(X0,X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | v3_pre_topc(u1_struct_0(X0),X1)
% 8.07/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f128]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_288,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(X0),X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v1_tsep_1(X0,X1)
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_26,c_36]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_289,plain,
% 8.07/1.50      ( ~ v1_tsep_1(X0,X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | v3_pre_topc(u1_struct_0(X0),X1)
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_288]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_42,negated_conjecture,
% 8.07/1.50      ( v1_tsep_1(sK3,sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(cnf_transformation,[],[f123]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_384,plain,
% 8.07/1.50      ( v1_tsep_1(sK3,sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(prop_impl,[status(thm)],[c_42]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_812,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | v3_pre_topc(u1_struct_0(X0),X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | sK3 != X0
% 8.07/1.50      | sK2 != X1 ),
% 8.07/1.50      inference(resolution_lifted,[status(thm)],[c_289,c_384]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_813,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | v3_pre_topc(u1_struct_0(sK3),sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(unflattening,[status(thm)],[c_812]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_815,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_813,c_45,c_43]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_817,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9,plain,
% 8.07/1.50      ( ~ v3_pre_topc(X0,X1)
% 8.07/1.50      | r2_hidden(X0,u1_pre_topc(X1))
% 8.07/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f86]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7141,plain,
% 8.07/1.50      ( v3_pre_topc(X0,X1) != iProver_top
% 8.07/1.50      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 8.07/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14314,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14306,c_7141]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7578,plain,
% 8.07/1.50      ( ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 8.07/1.50      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7579,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_7578]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16303,plain,
% 8.07/1.50      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 8.07/1.50      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14314,c_50,c_52,c_7579,c_7918]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16304,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_16303]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_31,plain,
% 8.07/1.50      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 8.07/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f108]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7126,plain,
% 8.07/1.50      ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
% 8.07/1.50      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14315,plain,
% 8.07/1.50      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14306,c_7126]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7718,plain,
% 8.07/1.50      ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 8.07/1.50      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ v2_pre_topc(sK2)
% 8.07/1.50      | v2_struct_0(sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_31]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7722,plain,
% 8.07/1.50      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_7718]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_33093,plain,
% 8.07/1.50      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 8.07/1.50      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14315,c_48,c_49,c_50,c_52,c_7722,c_7918]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_33094,plain,
% 8.07/1.50      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_33093]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_32,plain,
% 8.07/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f111]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7125,plain,
% 8.07/1.50      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14316,plain,
% 8.07/1.50      ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK3))) = k5_tmap_1(sK2,u1_struct_0(sK3))
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14306,c_7125]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14331,plain,
% 8.07/1.50      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(light_normalisation,[status(thm)],[c_14316,c_11904]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14832,plain,
% 8.07/1.50      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14331,c_48,c_49,c_50]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_33097,plain,
% 8.07/1.50      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 8.07/1.50      inference(demodulation,[status(thm)],[c_33094,c_14832]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_24,plain,
% 8.07/1.50      ( v1_tsep_1(X0,X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | sK1(X1,X0) = u1_struct_0(X0) ),
% 8.07/1.50      inference(cnf_transformation,[],[f103]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_40,negated_conjecture,
% 8.07/1.50      ( ~ v1_tsep_1(sK3,sK2)
% 8.07/1.50      | ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(cnf_transformation,[],[f125]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_382,plain,
% 8.07/1.50      ( ~ v1_tsep_1(sK3,sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(prop_impl,[status(thm)],[c_43,c_40]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_787,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | sK1(X1,X0) = u1_struct_0(X0)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | sK3 != X0
% 8.07/1.50      | sK2 != X1 ),
% 8.07/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_382]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_788,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | sK1(sK2,sK3) = u1_struct_0(sK3)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(unflattening,[status(thm)],[c_787]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_23,plain,
% 8.07/1.50      ( v1_tsep_1(X0,X1)
% 8.07/1.50      | ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f104]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_798,plain,
% 8.07/1.50      ( ~ m1_pre_topc(X0,X1)
% 8.07/1.50      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | sK3 != X0
% 8.07/1.50      | sK2 != X1 ),
% 8.07/1.50      inference(resolution_lifted,[status(thm)],[c_23,c_382]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_799,plain,
% 8.07/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 8.07/1.50      | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 8.07/1.50      | ~ l1_pre_topc(sK2)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(unflattening,[status(thm)],[c_798]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_800,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 8.07/1.50      | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6359,plain,
% 8.07/1.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 8.07/1.50      theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6375,plain,
% 8.07/1.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6359]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6360,plain,
% 8.07/1.50      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 8.07/1.50      theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6376,plain,
% 8.07/1.50      ( u1_pre_topc(sK2) = u1_pre_topc(sK2) | sK2 != sK2 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6360]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6353,plain,( X0 = X0 ),theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6388,plain,
% 8.07/1.50      ( sK2 = sK2 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6353]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8440,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6353]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6364,plain,
% 8.07/1.50      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.07/1.50      theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7629,plain,
% 8.07/1.50      ( v3_pre_topc(X0,X1)
% 8.07/1.50      | ~ v3_pre_topc(u1_struct_0(X2),X3)
% 8.07/1.50      | X1 != X3
% 8.07/1.50      | X0 != u1_struct_0(X2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6364]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8112,plain,
% 8.07/1.50      ( v3_pre_topc(sK1(X0,X1),X2)
% 8.07/1.50      | ~ v3_pre_topc(u1_struct_0(X1),X3)
% 8.07/1.50      | X2 != X3
% 8.07/1.50      | sK1(X0,X1) != u1_struct_0(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7629]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9665,plain,
% 8.07/1.50      ( v3_pre_topc(sK1(sK2,sK3),X0)
% 8.07/1.50      | ~ v3_pre_topc(u1_struct_0(sK3),X1)
% 8.07/1.50      | X0 != X1
% 8.07/1.50      | sK1(sK2,sK3) != u1_struct_0(sK3) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8112]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9666,plain,
% 8.07/1.50      ( X0 != X1
% 8.07/1.50      | sK1(sK2,sK3) != u1_struct_0(sK3)
% 8.07/1.50      | v3_pre_topc(sK1(sK2,sK3),X0) = iProver_top
% 8.07/1.50      | v3_pre_topc(u1_struct_0(sK3),X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_9665]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9668,plain,
% 8.07/1.50      ( sK1(sK2,sK3) != u1_struct_0(sK3)
% 8.07/1.50      | sK2 != sK2
% 8.07/1.50      | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 8.07/1.50      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_9666]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6354,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7945,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != X0
% 8.07/1.50      | k8_tmap_1(sK2,sK3) = g1_pre_topc(X1,X2)
% 8.07/1.50      | g1_pre_topc(X1,X2) != X0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6354]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8442,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != k8_tmap_1(X0,X1)
% 8.07/1.50      | k8_tmap_1(sK2,sK3) = g1_pre_topc(X2,X3)
% 8.07/1.50      | g1_pre_topc(X2,X3) != k8_tmap_1(X0,X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7945]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_11591,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != k8_tmap_1(X0,X1)
% 8.07/1.50      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) != k8_tmap_1(X0,X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8442]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_15600,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_11591]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8,plain,
% 8.07/1.50      ( v3_pre_topc(X0,X1)
% 8.07/1.50      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 8.07/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ l1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f87]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7142,plain,
% 8.07/1.50      ( v3_pre_topc(X0,X1) = iProver_top
% 8.07/1.50      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 8.07/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.07/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14313,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14306,c_7142]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7719,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 8.07/1.50      | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 8.07/1.50      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.07/1.50      | ~ l1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7720,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_7719]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16296,plain,
% 8.07/1.50      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 8.07/1.50      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14313,c_50,c_52,c_7720,c_7918]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_16297,plain,
% 8.07/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 8.07/1.50      inference(renaming,[status(thm)],[c_16296]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7576,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != X0
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6354]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7735,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(X0,X1)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7576]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_12483,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7735]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17475,plain,
% 8.07/1.50      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 8.07/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_12483]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6361,plain,
% 8.07/1.50      ( X0 != X1 | X2 != X3 | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
% 8.07/1.50      theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7773,plain,
% 8.07/1.50      ( X0 != u1_pre_topc(X1)
% 8.07/1.50      | X2 != u1_struct_0(X1)
% 8.07/1.50      | g1_pre_topc(X2,X0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6361]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8145,plain,
% 8.07/1.50      ( X0 != u1_struct_0(X1)
% 8.07/1.50      | g1_pre_topc(X0,u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 8.07/1.50      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7773]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8723,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
% 8.07/1.50      | u1_pre_topc(X1) != u1_pre_topc(X2)
% 8.07/1.50      | u1_struct_0(X0) != u1_struct_0(X2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8145]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21806,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 8.07/1.50      | u1_pre_topc(X1) != u1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8723]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21807,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 8.07/1.50      | u1_pre_topc(sK2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_21806]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7833,plain,
% 8.07/1.50      ( X0 != X1 | X0 = u1_pre_topc(X2) | u1_pre_topc(X2) != X1 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6354]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8061,plain,
% 8.07/1.50      ( X0 != u1_pre_topc(X1)
% 8.07/1.50      | X0 = u1_pre_topc(X2)
% 8.07/1.50      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7833]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8576,plain,
% 8.07/1.50      ( u1_pre_topc(X0) != u1_pre_topc(X1)
% 8.07/1.50      | u1_pre_topc(X2) != u1_pre_topc(X1)
% 8.07/1.50      | u1_pre_topc(X0) = u1_pre_topc(X2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8061]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_31149,plain,
% 8.07/1.50      ( u1_pre_topc(X0) != u1_pre_topc(X1)
% 8.07/1.50      | u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8576]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_31150,plain,
% 8.07/1.50      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 8.07/1.50      | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_31149]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7855,plain,
% 8.07/1.50      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6354]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8077,plain,
% 8.07/1.50      ( X0 != u1_struct_0(X1)
% 8.07/1.50      | X0 = u1_struct_0(X2)
% 8.07/1.50      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_7855]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_8614,plain,
% 8.07/1.50      ( u1_struct_0(X0) != u1_struct_0(X1)
% 8.07/1.50      | u1_struct_0(X2) != u1_struct_0(X1)
% 8.07/1.50      | u1_struct_0(X0) = u1_struct_0(X2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8077]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_31777,plain,
% 8.07/1.50      ( u1_struct_0(X0) != u1_struct_0(X1)
% 8.07/1.50      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(X1) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8614]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_31778,plain,
% 8.07/1.50      ( u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2)
% 8.07/1.50      | u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3))
% 8.07/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_31777]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_33101,plain,
% 8.07/1.50      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_33097,c_47,c_48,c_46,c_49,c_45,c_50,c_43,c_52,c_788,
% 8.07/1.50                 c_800,c_6375,c_6376,c_6388,c_8440,c_8872,c_9668,c_10158,
% 8.07/1.50                 c_12029,c_14322,c_15600,c_16297,c_17475,c_21807,c_31150,
% 8.07/1.50                 c_31778]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_31144,plain,
% 8.07/1.50      ( X0 != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6360]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_38671,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 8.07/1.50      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_31144]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_41719,plain,
% 8.07/1.50      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_39567,c_47,c_48,c_46,c_49,c_45,c_50,c_43,c_52,c_788,
% 8.07/1.50                 c_800,c_817,c_6375,c_6376,c_6388,c_7579,c_7918,c_8440,
% 8.07/1.50                 c_8872,c_9668,c_10158,c_12029,c_14322,c_15600,c_16297,
% 8.07/1.50                 c_17475,c_21807,c_31150,c_31778,c_33097,c_38671]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_42399,plain,
% 8.07/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 8.07/1.50      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
% 8.07/1.50      inference(demodulation,[status(thm)],[c_42397,c_41719]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_42405,plain,
% 8.07/1.50      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 8.07/1.50      inference(equality_resolution,[status(thm)],[c_42399]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_30,plain,
% 8.07/1.50      ( r2_hidden(X0,u1_pre_topc(X1))
% 8.07/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.07/1.50      | ~ v2_pre_topc(X1)
% 8.07/1.50      | v2_struct_0(X1)
% 8.07/1.50      | ~ l1_pre_topc(X1)
% 8.07/1.50      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 8.07/1.50      inference(cnf_transformation,[],[f109]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_7127,plain,
% 8.07/1.50      ( k5_tmap_1(X0,X1) != u1_pre_topc(X0)
% 8.07/1.50      | r2_hidden(X1,u1_pre_topc(X0)) = iProver_top
% 8.07/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.07/1.50      | v2_pre_topc(X0) != iProver_top
% 8.07/1.50      | v2_struct_0(X0) = iProver_top
% 8.07/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14835,plain,
% 8.07/1.50      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 8.07/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 8.07/1.50      | v2_pre_topc(sK2) != iProver_top
% 8.07/1.50      | v2_struct_0(sK2) = iProver_top
% 8.07/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14832,c_7127]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_17515,plain,
% 8.07/1.50      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 8.07/1.50      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_14835,c_48,c_49,c_50,c_52,c_7918]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(contradiction,plain,
% 8.07/1.50      ( $false ),
% 8.07/1.50      inference(minisat,[status(thm)],[c_42405,c_33101,c_17515]) ).
% 8.07/1.50  
% 8.07/1.50  
% 8.07/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.07/1.50  
% 8.07/1.50  ------                               Statistics
% 8.07/1.50  
% 8.07/1.50  ------ General
% 8.07/1.50  
% 8.07/1.50  abstr_ref_over_cycles:                  0
% 8.07/1.50  abstr_ref_under_cycles:                 0
% 8.07/1.50  gc_basic_clause_elim:                   0
% 8.07/1.50  forced_gc_time:                         0
% 8.07/1.50  parsing_time:                           0.016
% 8.07/1.50  unif_index_cands_time:                  0.
% 8.07/1.50  unif_index_add_time:                    0.
% 8.07/1.50  orderings_time:                         0.
% 8.07/1.50  out_proof_time:                         0.028
% 8.07/1.50  total_time:                             0.979
% 8.07/1.50  num_of_symbols:                         54
% 8.07/1.50  num_of_terms:                           23131
% 8.07/1.50  
% 8.07/1.50  ------ Preprocessing
% 8.07/1.50  
% 8.07/1.50  num_of_splits:                          0
% 8.07/1.50  num_of_split_atoms:                     0
% 8.07/1.50  num_of_reused_defs:                     0
% 8.07/1.50  num_eq_ax_congr_red:                    25
% 8.07/1.50  num_of_sem_filtered_clauses:            1
% 8.07/1.50  num_of_subtypes:                        0
% 8.07/1.50  monotx_restored_types:                  0
% 8.07/1.50  sat_num_of_epr_types:                   0
% 8.07/1.50  sat_num_of_non_cyclic_types:            0
% 8.07/1.50  sat_guarded_non_collapsed_types:        0
% 8.07/1.50  num_pure_diseq_elim:                    0
% 8.07/1.50  simp_replaced_by:                       0
% 8.07/1.50  res_preprocessed:                       211
% 8.07/1.50  prep_upred:                             0
% 8.07/1.50  prep_unflattend:                        239
% 8.07/1.50  smt_new_axioms:                         0
% 8.07/1.50  pred_elim_cands:                        9
% 8.07/1.50  pred_elim:                              3
% 8.07/1.50  pred_elim_cl:                           2
% 8.07/1.50  pred_elim_cycles:                       10
% 8.07/1.50  merged_defs:                            2
% 8.07/1.50  merged_defs_ncl:                        0
% 8.07/1.50  bin_hyper_res:                          2
% 8.07/1.50  prep_cycles:                            4
% 8.07/1.50  pred_elim_time:                         0.098
% 8.07/1.50  splitting_time:                         0.
% 8.07/1.50  sem_filter_time:                        0.
% 8.07/1.50  monotx_time:                            0.
% 8.07/1.50  subtype_inf_time:                       0.
% 8.07/1.50  
% 8.07/1.50  ------ Problem properties
% 8.07/1.50  
% 8.07/1.50  clauses:                                43
% 8.07/1.50  conjectures:                            5
% 8.07/1.50  epr:                                    12
% 8.07/1.50  horn:                                   27
% 8.07/1.50  ground:                                 9
% 8.07/1.50  unary:                                  5
% 8.07/1.50  binary:                                 7
% 8.07/1.50  lits:                                   155
% 8.07/1.50  lits_eq:                                21
% 8.07/1.50  fd_pure:                                0
% 8.07/1.50  fd_pseudo:                              0
% 8.07/1.50  fd_cond:                                0
% 8.07/1.50  fd_pseudo_cond:                         5
% 8.07/1.50  ac_symbols:                             0
% 8.07/1.50  
% 8.07/1.50  ------ Propositional Solver
% 8.07/1.50  
% 8.07/1.50  prop_solver_calls:                      32
% 8.07/1.50  prop_fast_solver_calls:                 4537
% 8.07/1.50  smt_solver_calls:                       0
% 8.07/1.50  smt_fast_solver_calls:                  0
% 8.07/1.50  prop_num_of_clauses:                    9190
% 8.07/1.50  prop_preprocess_simplified:             19484
% 8.07/1.50  prop_fo_subsumed:                       326
% 8.07/1.50  prop_solver_time:                       0.
% 8.07/1.50  smt_solver_time:                        0.
% 8.07/1.50  smt_fast_solver_time:                   0.
% 8.07/1.50  prop_fast_solver_time:                  0.
% 8.07/1.50  prop_unsat_core_time:                   0.001
% 8.07/1.50  
% 8.07/1.50  ------ QBF
% 8.07/1.50  
% 8.07/1.50  qbf_q_res:                              0
% 8.07/1.50  qbf_num_tautologies:                    0
% 8.07/1.50  qbf_prep_cycles:                        0
% 8.07/1.50  
% 8.07/1.50  ------ BMC1
% 8.07/1.50  
% 8.07/1.50  bmc1_current_bound:                     -1
% 8.07/1.50  bmc1_last_solved_bound:                 -1
% 8.07/1.50  bmc1_unsat_core_size:                   -1
% 8.07/1.50  bmc1_unsat_core_parents_size:           -1
% 8.07/1.50  bmc1_merge_next_fun:                    0
% 8.07/1.50  bmc1_unsat_core_clauses_time:           0.
% 8.07/1.50  
% 8.07/1.50  ------ Instantiation
% 8.07/1.50  
% 8.07/1.50  inst_num_of_clauses:                    2676
% 8.07/1.50  inst_num_in_passive:                    740
% 8.07/1.50  inst_num_in_active:                     1282
% 8.07/1.50  inst_num_in_unprocessed:                654
% 8.07/1.50  inst_num_of_loops:                      1620
% 8.07/1.50  inst_num_of_learning_restarts:          0
% 8.07/1.50  inst_num_moves_active_passive:          333
% 8.07/1.50  inst_lit_activity:                      0
% 8.07/1.50  inst_lit_activity_moves:                0
% 8.07/1.50  inst_num_tautologies:                   0
% 8.07/1.50  inst_num_prop_implied:                  0
% 8.07/1.50  inst_num_existing_simplified:           0
% 8.07/1.50  inst_num_eq_res_simplified:             0
% 8.07/1.50  inst_num_child_elim:                    0
% 8.07/1.50  inst_num_of_dismatching_blockings:      6158
% 8.07/1.50  inst_num_of_non_proper_insts:           7421
% 8.07/1.50  inst_num_of_duplicates:                 0
% 8.07/1.50  inst_inst_num_from_inst_to_res:         0
% 8.07/1.50  inst_dismatching_checking_time:         0.
% 8.07/1.50  
% 8.07/1.50  ------ Resolution
% 8.07/1.50  
% 8.07/1.50  res_num_of_clauses:                     0
% 8.07/1.50  res_num_in_passive:                     0
% 8.07/1.50  res_num_in_active:                      0
% 8.07/1.50  res_num_of_loops:                       215
% 8.07/1.50  res_forward_subset_subsumed:            450
% 8.07/1.50  res_backward_subset_subsumed:           2
% 8.07/1.50  res_forward_subsumed:                   0
% 8.07/1.50  res_backward_subsumed:                  0
% 8.07/1.50  res_forward_subsumption_resolution:     6
% 8.07/1.50  res_backward_subsumption_resolution:    0
% 8.07/1.50  res_clause_to_clause_subsumption:       4155
% 8.07/1.50  res_orphan_elimination:                 0
% 8.07/1.50  res_tautology_del:                      680
% 8.07/1.50  res_num_eq_res_simplified:              0
% 8.07/1.50  res_num_sel_changes:                    0
% 8.07/1.50  res_moves_from_active_to_pass:          0
% 8.07/1.50  
% 8.07/1.50  ------ Superposition
% 8.07/1.50  
% 8.07/1.50  sup_time_total:                         0.
% 8.07/1.50  sup_time_generating:                    0.
% 8.07/1.50  sup_time_sim_full:                      0.
% 8.07/1.50  sup_time_sim_immed:                     0.
% 8.07/1.50  
% 8.07/1.50  sup_num_of_clauses:                     767
% 8.07/1.50  sup_num_in_active:                      281
% 8.07/1.50  sup_num_in_passive:                     486
% 8.07/1.50  sup_num_of_loops:                       323
% 8.07/1.50  sup_fw_superposition:                   755
% 8.07/1.50  sup_bw_superposition:                   849
% 8.07/1.50  sup_immediate_simplified:               599
% 8.07/1.50  sup_given_eliminated:                   1
% 8.07/1.50  comparisons_done:                       0
% 8.07/1.50  comparisons_avoided:                    23
% 8.07/1.50  
% 8.07/1.50  ------ Simplifications
% 8.07/1.50  
% 8.07/1.50  
% 8.07/1.50  sim_fw_subset_subsumed:                 141
% 8.07/1.50  sim_bw_subset_subsumed:                 42
% 8.07/1.50  sim_fw_subsumed:                        203
% 8.07/1.50  sim_bw_subsumed:                        17
% 8.07/1.50  sim_fw_subsumption_res:                 4
% 8.07/1.50  sim_bw_subsumption_res:                 0
% 8.07/1.50  sim_tautology_del:                      106
% 8.07/1.50  sim_eq_tautology_del:                   80
% 8.07/1.50  sim_eq_res_simp:                        0
% 8.07/1.50  sim_fw_demodulated:                     7
% 8.07/1.50  sim_bw_demodulated:                     36
% 8.07/1.50  sim_light_normalised:                   430
% 8.07/1.50  sim_joinable_taut:                      0
% 8.07/1.50  sim_joinable_simp:                      0
% 8.07/1.50  sim_ac_normalised:                      0
% 8.07/1.50  sim_smt_subsumption:                    0
% 8.07/1.50  
%------------------------------------------------------------------------------
