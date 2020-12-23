%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:21 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  226 (3310 expanded)
%              Number of clauses        :  136 ( 900 expanded)
%              Number of leaves         :   24 ( 957 expanded)
%              Depth                    :   32
%              Number of atoms          :  906 (24941 expanded)
%              Number of equality atoms :  321 (3056 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2))
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2))
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2))
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f57,f56,f55,f54])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f95,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1557,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1554,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_398,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_9,c_5,c_4])).

cnf(c_403,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_459,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_403])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_9,c_6,c_5,c_4])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_463])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_597,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_464,c_28])).

cnf(c_598,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | k1_relat_1(sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_1542,plain,
    ( k1_relat_1(sK3) = X0
    | v1_funct_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_2063,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1542])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_380,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_12,c_14])).

cnf(c_2001,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_2002,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_2162,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_37,c_39,c_46,c_2002])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_198,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_13])).

cnf(c_199,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_1544,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_3133,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_1544])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3810,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_42])).

cnf(c_3811,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3810])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2169,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_2162,c_25])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1558,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3248,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_1558])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1552,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1559,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2589,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_1559])).

cnf(c_3571,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3248,c_42,c_2589])).

cnf(c_3572,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3571])).

cnf(c_3820,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3811,c_3572])).

cnf(c_3847,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_3820])).

cnf(c_53,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_55,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_3151,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_3272,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3248])).

cnf(c_4201,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3847,c_42,c_55,c_2589,c_3151,c_3272])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1556,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4206,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4201,c_1556])).

cnf(c_4214,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4206,c_2162])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1560,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3282,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_1560])).

cnf(c_4843,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4214,c_41,c_42,c_2589,c_3282])).

cnf(c_3966,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_1556])).

cnf(c_4412,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3966,c_41,c_42])).

cnf(c_4421,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_4412])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4540,plain,
    ( r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4421,c_42,c_44,c_55])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1564,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4545,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_1564])).

cnf(c_5079,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4843,c_4545])).

cnf(c_3848,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_3820])).

cnf(c_6791,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5079,c_42,c_55,c_2589,c_3151,c_3272,c_3848])).

cnf(c_2166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2162,c_1554])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_615,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_616,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_1541,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2346,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_1541])).

cnf(c_2379,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2346,c_2162])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3042,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
    | k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_40,c_41,c_42])).

cnf(c_3043,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3042])).

cnf(c_3053,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_3043])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_652,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_1540,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1965,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1554,c_1540])).

cnf(c_2165,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_2162,c_1965])).

cnf(c_3069,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3053,c_2165])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1772,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_1027,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1835,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_1929,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_1035,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_1810,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | X2 != u1_struct_0(sK0)
    | X1 != u1_struct_0(sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_1859,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | X1 != u1_struct_0(sK0)
    | X0 != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_1928,plain,
    ( v1_funct_2(sK3,X0,u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | X0 != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_2077,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_relat_1(sK3) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_2078,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_relat_1(sK3) != u1_struct_0(sK1)
    | sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_4944,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3069,c_36,c_37,c_38,c_34,c_39,c_27,c_46,c_26,c_1772,c_1835,c_1929,c_2001,c_2078])).

cnf(c_4945,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4944])).

cnf(c_4953,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1552,c_4945])).

cnf(c_18,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_24,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_493,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK0) != X2
    | u1_struct_0(sK0) != X4
    | u1_struct_0(sK1) != X3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_494,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_663,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_494])).

cnf(c_1539,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_2168,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2162,c_1539])).

cnf(c_2900,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2168,c_37,c_39,c_2002])).

cnf(c_2901,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2900])).

cnf(c_4963,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4953,c_2901])).

cnf(c_6794,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) != sK3
    | v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6791,c_4963])).

cnf(c_1561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2492,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_1561])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1563,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1562,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3157,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1562])).

cnf(c_4226,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2492,c_3157])).

cnf(c_6823,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6794,c_4226])).

cnf(c_6824,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6823])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6824,c_2166,c_2078,c_2001,c_1929,c_1835,c_1772,c_26,c_46,c_27,c_34,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:44:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.16/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.98  
% 3.16/0.98  ------  iProver source info
% 3.16/0.98  
% 3.16/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.98  git: non_committed_changes: false
% 3.16/0.98  git: last_make_outside_of_git: false
% 3.16/0.98  
% 3.16/0.98  ------ 
% 3.16/0.98  
% 3.16/0.98  ------ Input Options
% 3.16/0.98  
% 3.16/0.98  --out_options                           all
% 3.16/0.98  --tptp_safe_out                         true
% 3.16/0.98  --problem_path                          ""
% 3.16/0.98  --include_path                          ""
% 3.16/0.98  --clausifier                            res/vclausify_rel
% 3.16/0.98  --clausifier_options                    --mode clausify
% 3.16/0.98  --stdin                                 false
% 3.16/0.98  --stats_out                             all
% 3.16/0.98  
% 3.16/0.98  ------ General Options
% 3.16/0.98  
% 3.16/0.98  --fof                                   false
% 3.16/0.98  --time_out_real                         305.
% 3.16/0.98  --time_out_virtual                      -1.
% 3.16/0.98  --symbol_type_check                     false
% 3.16/0.98  --clausify_out                          false
% 3.16/0.98  --sig_cnt_out                           false
% 3.16/0.98  --trig_cnt_out                          false
% 3.16/0.98  --trig_cnt_out_tolerance                1.
% 3.16/0.98  --trig_cnt_out_sk_spl                   false
% 3.16/0.98  --abstr_cl_out                          false
% 3.16/0.98  
% 3.16/0.98  ------ Global Options
% 3.16/0.98  
% 3.16/0.98  --schedule                              default
% 3.16/0.98  --add_important_lit                     false
% 3.16/0.98  --prop_solver_per_cl                    1000
% 3.16/0.98  --min_unsat_core                        false
% 3.16/0.98  --soft_assumptions                      false
% 3.16/0.98  --soft_lemma_size                       3
% 3.16/0.98  --prop_impl_unit_size                   0
% 3.16/0.98  --prop_impl_unit                        []
% 3.16/0.98  --share_sel_clauses                     true
% 3.16/0.98  --reset_solvers                         false
% 3.16/0.98  --bc_imp_inh                            [conj_cone]
% 3.16/0.98  --conj_cone_tolerance                   3.
% 3.16/0.98  --extra_neg_conj                        none
% 3.16/0.98  --large_theory_mode                     true
% 3.16/0.98  --prolific_symb_bound                   200
% 3.16/0.98  --lt_threshold                          2000
% 3.16/0.98  --clause_weak_htbl                      true
% 3.16/0.98  --gc_record_bc_elim                     false
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing Options
% 3.16/0.98  
% 3.16/0.98  --preprocessing_flag                    true
% 3.16/0.98  --time_out_prep_mult                    0.1
% 3.16/0.98  --splitting_mode                        input
% 3.16/0.98  --splitting_grd                         true
% 3.16/0.98  --splitting_cvd                         false
% 3.16/0.98  --splitting_cvd_svl                     false
% 3.16/0.98  --splitting_nvd                         32
% 3.16/0.98  --sub_typing                            true
% 3.16/0.98  --prep_gs_sim                           true
% 3.16/0.98  --prep_unflatten                        true
% 3.16/0.98  --prep_res_sim                          true
% 3.16/0.98  --prep_upred                            true
% 3.16/0.98  --prep_sem_filter                       exhaustive
% 3.16/0.98  --prep_sem_filter_out                   false
% 3.16/0.98  --pred_elim                             true
% 3.16/0.98  --res_sim_input                         true
% 3.16/0.98  --eq_ax_congr_red                       true
% 3.16/0.98  --pure_diseq_elim                       true
% 3.16/0.98  --brand_transform                       false
% 3.16/0.98  --non_eq_to_eq                          false
% 3.16/0.98  --prep_def_merge                        true
% 3.16/0.98  --prep_def_merge_prop_impl              false
% 3.16/0.98  --prep_def_merge_mbd                    true
% 3.16/0.98  --prep_def_merge_tr_red                 false
% 3.16/0.98  --prep_def_merge_tr_cl                  false
% 3.16/0.98  --smt_preprocessing                     true
% 3.16/0.98  --smt_ac_axioms                         fast
% 3.16/0.98  --preprocessed_out                      false
% 3.16/0.98  --preprocessed_stats                    false
% 3.16/0.98  
% 3.16/0.98  ------ Abstraction refinement Options
% 3.16/0.98  
% 3.16/0.98  --abstr_ref                             []
% 3.16/0.98  --abstr_ref_prep                        false
% 3.16/0.98  --abstr_ref_until_sat                   false
% 3.16/0.98  --abstr_ref_sig_restrict                funpre
% 3.16/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.98  --abstr_ref_under                       []
% 3.16/0.98  
% 3.16/0.98  ------ SAT Options
% 3.16/0.98  
% 3.16/0.98  --sat_mode                              false
% 3.16/0.98  --sat_fm_restart_options                ""
% 3.16/0.98  --sat_gr_def                            false
% 3.16/0.98  --sat_epr_types                         true
% 3.16/0.98  --sat_non_cyclic_types                  false
% 3.16/0.98  --sat_finite_models                     false
% 3.16/0.98  --sat_fm_lemmas                         false
% 3.16/0.98  --sat_fm_prep                           false
% 3.16/0.98  --sat_fm_uc_incr                        true
% 3.16/0.98  --sat_out_model                         small
% 3.16/0.98  --sat_out_clauses                       false
% 3.16/0.98  
% 3.16/0.98  ------ QBF Options
% 3.16/0.98  
% 3.16/0.98  --qbf_mode                              false
% 3.16/0.98  --qbf_elim_univ                         false
% 3.16/0.98  --qbf_dom_inst                          none
% 3.16/0.98  --qbf_dom_pre_inst                      false
% 3.16/0.98  --qbf_sk_in                             false
% 3.16/0.98  --qbf_pred_elim                         true
% 3.16/0.98  --qbf_split                             512
% 3.16/0.98  
% 3.16/0.98  ------ BMC1 Options
% 3.16/0.98  
% 3.16/0.98  --bmc1_incremental                      false
% 3.16/0.98  --bmc1_axioms                           reachable_all
% 3.16/0.98  --bmc1_min_bound                        0
% 3.16/0.98  --bmc1_max_bound                        -1
% 3.16/0.98  --bmc1_max_bound_default                -1
% 3.16/0.98  --bmc1_symbol_reachability              true
% 3.16/0.98  --bmc1_property_lemmas                  false
% 3.16/0.98  --bmc1_k_induction                      false
% 3.16/0.98  --bmc1_non_equiv_states                 false
% 3.16/0.98  --bmc1_deadlock                         false
% 3.16/0.98  --bmc1_ucm                              false
% 3.16/0.98  --bmc1_add_unsat_core                   none
% 3.16/0.98  --bmc1_unsat_core_children              false
% 3.16/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.98  --bmc1_out_stat                         full
% 3.16/0.98  --bmc1_ground_init                      false
% 3.16/0.98  --bmc1_pre_inst_next_state              false
% 3.16/0.98  --bmc1_pre_inst_state                   false
% 3.16/0.98  --bmc1_pre_inst_reach_state             false
% 3.16/0.98  --bmc1_out_unsat_core                   false
% 3.16/0.98  --bmc1_aig_witness_out                  false
% 3.16/0.98  --bmc1_verbose                          false
% 3.16/0.98  --bmc1_dump_clauses_tptp                false
% 3.16/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.98  --bmc1_dump_file                        -
% 3.16/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.98  --bmc1_ucm_extend_mode                  1
% 3.16/0.98  --bmc1_ucm_init_mode                    2
% 3.16/0.98  --bmc1_ucm_cone_mode                    none
% 3.16/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.98  --bmc1_ucm_relax_model                  4
% 3.16/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.98  --bmc1_ucm_layered_model                none
% 3.16/0.98  --bmc1_ucm_max_lemma_size               10
% 3.16/0.98  
% 3.16/0.98  ------ AIG Options
% 3.16/0.98  
% 3.16/0.98  --aig_mode                              false
% 3.16/0.98  
% 3.16/0.98  ------ Instantiation Options
% 3.16/0.98  
% 3.16/0.98  --instantiation_flag                    true
% 3.16/0.98  --inst_sos_flag                         false
% 3.16/0.98  --inst_sos_phase                        true
% 3.16/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel_side                     num_symb
% 3.16/0.98  --inst_solver_per_active                1400
% 3.16/0.98  --inst_solver_calls_frac                1.
% 3.16/0.98  --inst_passive_queue_type               priority_queues
% 3.16/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.98  --inst_passive_queues_freq              [25;2]
% 3.16/0.98  --inst_dismatching                      true
% 3.16/0.98  --inst_eager_unprocessed_to_passive     true
% 3.16/0.98  --inst_prop_sim_given                   true
% 3.16/0.98  --inst_prop_sim_new                     false
% 3.16/0.98  --inst_subs_new                         false
% 3.16/0.98  --inst_eq_res_simp                      false
% 3.16/0.98  --inst_subs_given                       false
% 3.16/0.98  --inst_orphan_elimination               true
% 3.16/0.98  --inst_learning_loop_flag               true
% 3.16/0.98  --inst_learning_start                   3000
% 3.16/0.98  --inst_learning_factor                  2
% 3.16/0.98  --inst_start_prop_sim_after_learn       3
% 3.16/0.98  --inst_sel_renew                        solver
% 3.16/0.98  --inst_lit_activity_flag                true
% 3.16/0.98  --inst_restr_to_given                   false
% 3.16/0.98  --inst_activity_threshold               500
% 3.16/0.98  --inst_out_proof                        true
% 3.16/0.98  
% 3.16/0.98  ------ Resolution Options
% 3.16/0.98  
% 3.16/0.98  --resolution_flag                       true
% 3.16/0.98  --res_lit_sel                           adaptive
% 3.16/0.98  --res_lit_sel_side                      none
% 3.16/0.98  --res_ordering                          kbo
% 3.16/0.98  --res_to_prop_solver                    active
% 3.16/0.98  --res_prop_simpl_new                    false
% 3.16/0.98  --res_prop_simpl_given                  true
% 3.16/0.98  --res_passive_queue_type                priority_queues
% 3.16/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.98  --res_passive_queues_freq               [15;5]
% 3.16/0.98  --res_forward_subs                      full
% 3.16/0.98  --res_backward_subs                     full
% 3.16/0.98  --res_forward_subs_resolution           true
% 3.16/0.98  --res_backward_subs_resolution          true
% 3.16/0.98  --res_orphan_elimination                true
% 3.16/0.98  --res_time_limit                        2.
% 3.16/0.98  --res_out_proof                         true
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Options
% 3.16/0.98  
% 3.16/0.98  --superposition_flag                    true
% 3.16/0.98  --sup_passive_queue_type                priority_queues
% 3.16/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.98  --demod_completeness_check              fast
% 3.16/0.98  --demod_use_ground                      true
% 3.16/0.98  --sup_to_prop_solver                    passive
% 3.16/0.98  --sup_prop_simpl_new                    true
% 3.16/0.98  --sup_prop_simpl_given                  true
% 3.16/0.98  --sup_fun_splitting                     false
% 3.16/0.98  --sup_smt_interval                      50000
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Simplification Setup
% 3.16/0.98  
% 3.16/0.98  --sup_indices_passive                   []
% 3.16/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_full_bw                           [BwDemod]
% 3.16/0.98  --sup_immed_triv                        [TrivRules]
% 3.16/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_immed_bw_main                     []
% 3.16/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  
% 3.16/0.98  ------ Combination Options
% 3.16/0.98  
% 3.16/0.98  --comb_res_mult                         3
% 3.16/0.98  --comb_sup_mult                         2
% 3.16/0.98  --comb_inst_mult                        10
% 3.16/0.98  
% 3.16/0.98  ------ Debug Options
% 3.16/0.98  
% 3.16/0.98  --dbg_backtrace                         false
% 3.16/0.98  --dbg_dump_prop_clauses                 false
% 3.16/0.98  --dbg_dump_prop_clauses_file            -
% 3.16/0.98  --dbg_out_stat                          false
% 3.16/0.98  ------ Parsing...
% 3.16/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.98  ------ Proving...
% 3.16/0.98  ------ Problem Properties 
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  clauses                                 27
% 3.16/0.98  conjectures                             11
% 3.16/0.98  EPR                                     13
% 3.16/0.98  Horn                                    25
% 3.16/0.98  unary                                   12
% 3.16/0.98  binary                                  3
% 3.16/0.98  lits                                    72
% 3.16/0.98  lits eq                                 7
% 3.16/0.98  fd_pure                                 0
% 3.16/0.98  fd_pseudo                               0
% 3.16/0.98  fd_cond                                 1
% 3.16/0.98  fd_pseudo_cond                          1
% 3.16/0.98  AC symbols                              0
% 3.16/0.98  
% 3.16/0.98  ------ Schedule dynamic 5 is on 
% 3.16/0.98  
% 3.16/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  ------ 
% 3.16/0.98  Current options:
% 3.16/0.98  ------ 
% 3.16/0.98  
% 3.16/0.98  ------ Input Options
% 3.16/0.98  
% 3.16/0.98  --out_options                           all
% 3.16/0.98  --tptp_safe_out                         true
% 3.16/0.98  --problem_path                          ""
% 3.16/0.98  --include_path                          ""
% 3.16/0.98  --clausifier                            res/vclausify_rel
% 3.16/0.98  --clausifier_options                    --mode clausify
% 3.16/0.98  --stdin                                 false
% 3.16/0.98  --stats_out                             all
% 3.16/0.98  
% 3.16/0.98  ------ General Options
% 3.16/0.98  
% 3.16/0.98  --fof                                   false
% 3.16/0.98  --time_out_real                         305.
% 3.16/0.98  --time_out_virtual                      -1.
% 3.16/0.98  --symbol_type_check                     false
% 3.16/0.98  --clausify_out                          false
% 3.16/0.98  --sig_cnt_out                           false
% 3.16/0.98  --trig_cnt_out                          false
% 3.16/0.98  --trig_cnt_out_tolerance                1.
% 3.16/0.98  --trig_cnt_out_sk_spl                   false
% 3.16/0.98  --abstr_cl_out                          false
% 3.16/0.98  
% 3.16/0.98  ------ Global Options
% 3.16/0.98  
% 3.16/0.98  --schedule                              default
% 3.16/0.98  --add_important_lit                     false
% 3.16/0.98  --prop_solver_per_cl                    1000
% 3.16/0.98  --min_unsat_core                        false
% 3.16/0.98  --soft_assumptions                      false
% 3.16/0.98  --soft_lemma_size                       3
% 3.16/0.98  --prop_impl_unit_size                   0
% 3.16/0.98  --prop_impl_unit                        []
% 3.16/0.98  --share_sel_clauses                     true
% 3.16/0.98  --reset_solvers                         false
% 3.16/0.98  --bc_imp_inh                            [conj_cone]
% 3.16/0.98  --conj_cone_tolerance                   3.
% 3.16/0.98  --extra_neg_conj                        none
% 3.16/0.98  --large_theory_mode                     true
% 3.16/0.98  --prolific_symb_bound                   200
% 3.16/0.98  --lt_threshold                          2000
% 3.16/0.98  --clause_weak_htbl                      true
% 3.16/0.98  --gc_record_bc_elim                     false
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing Options
% 3.16/0.98  
% 3.16/0.98  --preprocessing_flag                    true
% 3.16/0.98  --time_out_prep_mult                    0.1
% 3.16/0.98  --splitting_mode                        input
% 3.16/0.98  --splitting_grd                         true
% 3.16/0.98  --splitting_cvd                         false
% 3.16/0.98  --splitting_cvd_svl                     false
% 3.16/0.98  --splitting_nvd                         32
% 3.16/0.98  --sub_typing                            true
% 3.16/0.98  --prep_gs_sim                           true
% 3.16/0.98  --prep_unflatten                        true
% 3.16/0.98  --prep_res_sim                          true
% 3.16/0.98  --prep_upred                            true
% 3.16/0.98  --prep_sem_filter                       exhaustive
% 3.16/0.98  --prep_sem_filter_out                   false
% 3.16/0.98  --pred_elim                             true
% 3.16/0.98  --res_sim_input                         true
% 3.16/0.98  --eq_ax_congr_red                       true
% 3.16/0.98  --pure_diseq_elim                       true
% 3.16/0.98  --brand_transform                       false
% 3.16/0.98  --non_eq_to_eq                          false
% 3.16/0.98  --prep_def_merge                        true
% 3.16/0.98  --prep_def_merge_prop_impl              false
% 3.16/0.98  --prep_def_merge_mbd                    true
% 3.16/0.98  --prep_def_merge_tr_red                 false
% 3.16/0.98  --prep_def_merge_tr_cl                  false
% 3.16/0.98  --smt_preprocessing                     true
% 3.16/0.98  --smt_ac_axioms                         fast
% 3.16/0.98  --preprocessed_out                      false
% 3.16/0.98  --preprocessed_stats                    false
% 3.16/0.98  
% 3.16/0.98  ------ Abstraction refinement Options
% 3.16/0.98  
% 3.16/0.98  --abstr_ref                             []
% 3.16/0.98  --abstr_ref_prep                        false
% 3.16/0.98  --abstr_ref_until_sat                   false
% 3.16/0.98  --abstr_ref_sig_restrict                funpre
% 3.16/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.98  --abstr_ref_under                       []
% 3.16/0.98  
% 3.16/0.98  ------ SAT Options
% 3.16/0.98  
% 3.16/0.98  --sat_mode                              false
% 3.16/0.98  --sat_fm_restart_options                ""
% 3.16/0.98  --sat_gr_def                            false
% 3.16/0.98  --sat_epr_types                         true
% 3.16/0.98  --sat_non_cyclic_types                  false
% 3.16/0.98  --sat_finite_models                     false
% 3.16/0.98  --sat_fm_lemmas                         false
% 3.16/0.98  --sat_fm_prep                           false
% 3.16/0.98  --sat_fm_uc_incr                        true
% 3.16/0.98  --sat_out_model                         small
% 3.16/0.98  --sat_out_clauses                       false
% 3.16/0.98  
% 3.16/0.98  ------ QBF Options
% 3.16/0.98  
% 3.16/0.98  --qbf_mode                              false
% 3.16/0.98  --qbf_elim_univ                         false
% 3.16/0.98  --qbf_dom_inst                          none
% 3.16/0.98  --qbf_dom_pre_inst                      false
% 3.16/0.98  --qbf_sk_in                             false
% 3.16/0.98  --qbf_pred_elim                         true
% 3.16/0.98  --qbf_split                             512
% 3.16/0.98  
% 3.16/0.98  ------ BMC1 Options
% 3.16/0.98  
% 3.16/0.98  --bmc1_incremental                      false
% 3.16/0.98  --bmc1_axioms                           reachable_all
% 3.16/0.98  --bmc1_min_bound                        0
% 3.16/0.98  --bmc1_max_bound                        -1
% 3.16/0.98  --bmc1_max_bound_default                -1
% 3.16/0.98  --bmc1_symbol_reachability              true
% 3.16/0.98  --bmc1_property_lemmas                  false
% 3.16/0.98  --bmc1_k_induction                      false
% 3.16/0.98  --bmc1_non_equiv_states                 false
% 3.16/0.98  --bmc1_deadlock                         false
% 3.16/0.98  --bmc1_ucm                              false
% 3.16/0.98  --bmc1_add_unsat_core                   none
% 3.16/0.98  --bmc1_unsat_core_children              false
% 3.16/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.98  --bmc1_out_stat                         full
% 3.16/0.98  --bmc1_ground_init                      false
% 3.16/0.98  --bmc1_pre_inst_next_state              false
% 3.16/0.98  --bmc1_pre_inst_state                   false
% 3.16/0.98  --bmc1_pre_inst_reach_state             false
% 3.16/0.98  --bmc1_out_unsat_core                   false
% 3.16/0.98  --bmc1_aig_witness_out                  false
% 3.16/0.98  --bmc1_verbose                          false
% 3.16/0.98  --bmc1_dump_clauses_tptp                false
% 3.16/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.98  --bmc1_dump_file                        -
% 3.16/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.98  --bmc1_ucm_extend_mode                  1
% 3.16/0.98  --bmc1_ucm_init_mode                    2
% 3.16/0.98  --bmc1_ucm_cone_mode                    none
% 3.16/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.98  --bmc1_ucm_relax_model                  4
% 3.16/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.98  --bmc1_ucm_layered_model                none
% 3.16/0.98  --bmc1_ucm_max_lemma_size               10
% 3.16/0.98  
% 3.16/0.98  ------ AIG Options
% 3.16/0.98  
% 3.16/0.98  --aig_mode                              false
% 3.16/0.98  
% 3.16/0.98  ------ Instantiation Options
% 3.16/0.98  
% 3.16/0.98  --instantiation_flag                    true
% 3.16/0.98  --inst_sos_flag                         false
% 3.16/0.98  --inst_sos_phase                        true
% 3.16/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel_side                     none
% 3.16/0.98  --inst_solver_per_active                1400
% 3.16/0.98  --inst_solver_calls_frac                1.
% 3.16/0.98  --inst_passive_queue_type               priority_queues
% 3.16/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.98  --inst_passive_queues_freq              [25;2]
% 3.16/0.98  --inst_dismatching                      true
% 3.16/0.98  --inst_eager_unprocessed_to_passive     true
% 3.16/0.98  --inst_prop_sim_given                   true
% 3.16/0.98  --inst_prop_sim_new                     false
% 3.16/0.98  --inst_subs_new                         false
% 3.16/0.98  --inst_eq_res_simp                      false
% 3.16/0.98  --inst_subs_given                       false
% 3.16/0.98  --inst_orphan_elimination               true
% 3.16/0.98  --inst_learning_loop_flag               true
% 3.16/0.98  --inst_learning_start                   3000
% 3.16/0.98  --inst_learning_factor                  2
% 3.16/0.98  --inst_start_prop_sim_after_learn       3
% 3.16/0.98  --inst_sel_renew                        solver
% 3.16/0.98  --inst_lit_activity_flag                true
% 3.16/0.98  --inst_restr_to_given                   false
% 3.16/0.98  --inst_activity_threshold               500
% 3.16/0.98  --inst_out_proof                        true
% 3.16/0.98  
% 3.16/0.98  ------ Resolution Options
% 3.16/0.98  
% 3.16/0.98  --resolution_flag                       false
% 3.16/0.98  --res_lit_sel                           adaptive
% 3.16/0.98  --res_lit_sel_side                      none
% 3.16/0.98  --res_ordering                          kbo
% 3.16/0.98  --res_to_prop_solver                    active
% 3.16/0.98  --res_prop_simpl_new                    false
% 3.16/0.98  --res_prop_simpl_given                  true
% 3.16/0.98  --res_passive_queue_type                priority_queues
% 3.16/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.98  --res_passive_queues_freq               [15;5]
% 3.16/0.98  --res_forward_subs                      full
% 3.16/0.98  --res_backward_subs                     full
% 3.16/0.98  --res_forward_subs_resolution           true
% 3.16/0.98  --res_backward_subs_resolution          true
% 3.16/0.98  --res_orphan_elimination                true
% 3.16/0.98  --res_time_limit                        2.
% 3.16/0.98  --res_out_proof                         true
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Options
% 3.16/0.98  
% 3.16/0.98  --superposition_flag                    true
% 3.16/0.98  --sup_passive_queue_type                priority_queues
% 3.16/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.98  --demod_completeness_check              fast
% 3.16/0.98  --demod_use_ground                      true
% 3.16/0.98  --sup_to_prop_solver                    passive
% 3.16/0.98  --sup_prop_simpl_new                    true
% 3.16/0.98  --sup_prop_simpl_given                  true
% 3.16/0.98  --sup_fun_splitting                     false
% 3.16/0.98  --sup_smt_interval                      50000
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Simplification Setup
% 3.16/0.98  
% 3.16/0.98  --sup_indices_passive                   []
% 3.16/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_full_bw                           [BwDemod]
% 3.16/0.98  --sup_immed_triv                        [TrivRules]
% 3.16/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_immed_bw_main                     []
% 3.16/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  
% 3.16/0.98  ------ Combination Options
% 3.16/0.98  
% 3.16/0.98  --comb_res_mult                         3
% 3.16/0.98  --comb_sup_mult                         2
% 3.16/0.98  --comb_inst_mult                        10
% 3.16/0.98  
% 3.16/0.98  ------ Debug Options
% 3.16/0.98  
% 3.16/0.98  --dbg_backtrace                         false
% 3.16/0.98  --dbg_dump_prop_clauses                 false
% 3.16/0.98  --dbg_dump_prop_clauses_file            -
% 3.16/0.98  --dbg_out_stat                          false
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  ------ Proving...
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  % SZS status Theorem for theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  fof(f16,axiom,(
% 3.16/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f43,plain,(
% 3.16/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.16/0.98    inference(ennf_transformation,[],[f16])).
% 3.16/0.98  
% 3.16/0.98  fof(f80,plain,(
% 3.16/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f43])).
% 3.16/0.98  
% 3.16/0.98  fof(f18,conjecture,(
% 3.16/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f19,negated_conjecture,(
% 3.16/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.16/0.98    inference(negated_conjecture,[],[f18])).
% 3.16/0.98  
% 3.16/0.98  fof(f46,plain,(
% 3.16/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.16/0.98    inference(ennf_transformation,[],[f19])).
% 3.16/0.98  
% 3.16/0.98  fof(f47,plain,(
% 3.16/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.16/0.98    inference(flattening,[],[f46])).
% 3.16/0.98  
% 3.16/0.98  fof(f57,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f56,plain,(
% 3.16/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f55,plain,(
% 3.16/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f54,plain,(
% 3.16/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f58,plain,(
% 3.16/0.98    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.16/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f57,f56,f55,f54])).
% 3.16/0.98  
% 3.16/0.98  fof(f93,plain,(
% 3.16/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f5,axiom,(
% 3.16/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f25,plain,(
% 3.16/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.16/0.98    inference(ennf_transformation,[],[f5])).
% 3.16/0.98  
% 3.16/0.98  fof(f26,plain,(
% 3.16/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.16/0.98    inference(flattening,[],[f25])).
% 3.16/0.98  
% 3.16/0.98  fof(f66,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f26])).
% 3.16/0.98  
% 3.16/0.98  fof(f4,axiom,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f20,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.16/0.98    inference(pure_predicate_removal,[],[f4])).
% 3.16/0.98  
% 3.16/0.98  fof(f24,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(ennf_transformation,[],[f20])).
% 3.16/0.98  
% 3.16/0.98  fof(f64,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f24])).
% 3.16/0.98  
% 3.16/0.98  fof(f6,axiom,(
% 3.16/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f27,plain,(
% 3.16/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/0.98    inference(ennf_transformation,[],[f6])).
% 3.16/0.98  
% 3.16/0.98  fof(f28,plain,(
% 3.16/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/0.98    inference(flattening,[],[f27])).
% 3.16/0.98  
% 3.16/0.98  fof(f50,plain,(
% 3.16/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/0.98    inference(nnf_transformation,[],[f28])).
% 3.16/0.98  
% 3.16/0.98  fof(f67,plain,(
% 3.16/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f50])).
% 3.16/0.98  
% 3.16/0.98  fof(f3,axiom,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f23,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(ennf_transformation,[],[f3])).
% 3.16/0.98  
% 3.16/0.98  fof(f63,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f23])).
% 3.16/0.98  
% 3.16/0.98  fof(f91,plain,(
% 3.16/0.98    v1_funct_1(sK3)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f83,plain,(
% 3.16/0.98    ~v2_struct_0(sK0)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f85,plain,(
% 3.16/0.98    l1_pre_topc(sK0)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f92,plain,(
% 3.16/0.98    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f9,axiom,(
% 3.16/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f33,plain,(
% 3.16/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.16/0.98    inference(ennf_transformation,[],[f9])).
% 3.16/0.98  
% 3.16/0.98  fof(f71,plain,(
% 3.16/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f33])).
% 3.16/0.98  
% 3.16/0.98  fof(f11,axiom,(
% 3.16/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f35,plain,(
% 3.16/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/0.98    inference(ennf_transformation,[],[f11])).
% 3.16/0.98  
% 3.16/0.98  fof(f36,plain,(
% 3.16/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/0.98    inference(flattening,[],[f35])).
% 3.16/0.98  
% 3.16/0.98  fof(f73,plain,(
% 3.16/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f36])).
% 3.16/0.98  
% 3.16/0.98  fof(f13,axiom,(
% 3.16/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f38,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.16/0.98    inference(ennf_transformation,[],[f13])).
% 3.16/0.98  
% 3.16/0.98  fof(f51,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.16/0.98    inference(nnf_transformation,[],[f38])).
% 3.16/0.98  
% 3.16/0.98  fof(f75,plain,(
% 3.16/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f51])).
% 3.16/0.98  
% 3.16/0.98  fof(f10,axiom,(
% 3.16/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f34,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.16/0.98    inference(ennf_transformation,[],[f10])).
% 3.16/0.98  
% 3.16/0.98  fof(f72,plain,(
% 3.16/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f34])).
% 3.16/0.98  
% 3.16/0.98  fof(f88,plain,(
% 3.16/0.98    l1_pre_topc(sK1)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f94,plain,(
% 3.16/0.98    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f12,axiom,(
% 3.16/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f37,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.16/0.98    inference(ennf_transformation,[],[f12])).
% 3.16/0.98  
% 3.16/0.98  fof(f74,plain,(
% 3.16/0.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f37])).
% 3.16/0.98  
% 3.16/0.98  fof(f90,plain,(
% 3.16/0.98    m1_pre_topc(sK2,sK1)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f17,axiom,(
% 3.16/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f44,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.98    inference(ennf_transformation,[],[f17])).
% 3.16/0.98  
% 3.16/0.98  fof(f45,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.98    inference(flattening,[],[f44])).
% 3.16/0.98  
% 3.16/0.98  fof(f53,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.98    inference(nnf_transformation,[],[f45])).
% 3.16/0.98  
% 3.16/0.98  fof(f82,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f53])).
% 3.16/0.98  
% 3.16/0.98  fof(f87,plain,(
% 3.16/0.98    v2_pre_topc(sK1)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f8,axiom,(
% 3.16/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f31,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.98    inference(ennf_transformation,[],[f8])).
% 3.16/0.98  
% 3.16/0.98  fof(f32,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.98    inference(flattening,[],[f31])).
% 3.16/0.98  
% 3.16/0.98  fof(f70,plain,(
% 3.16/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f32])).
% 3.16/0.98  
% 3.16/0.98  fof(f1,axiom,(
% 3.16/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f48,plain,(
% 3.16/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.98    inference(nnf_transformation,[],[f1])).
% 3.16/0.98  
% 3.16/0.98  fof(f49,plain,(
% 3.16/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.98    inference(flattening,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f61,plain,(
% 3.16/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f49])).
% 3.16/0.98  
% 3.16/0.98  fof(f15,axiom,(
% 3.16/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f41,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.16/0.98    inference(ennf_transformation,[],[f15])).
% 3.16/0.98  
% 3.16/0.98  fof(f42,plain,(
% 3.16/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.16/0.98    inference(flattening,[],[f41])).
% 3.16/0.98  
% 3.16/0.98  fof(f79,plain,(
% 3.16/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f42])).
% 3.16/0.98  
% 3.16/0.98  fof(f86,plain,(
% 3.16/0.98    ~v2_struct_0(sK1)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f7,axiom,(
% 3.16/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f29,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.16/0.98    inference(ennf_transformation,[],[f7])).
% 3.16/0.98  
% 3.16/0.98  fof(f30,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.16/0.98    inference(flattening,[],[f29])).
% 3.16/0.98  
% 3.16/0.98  fof(f69,plain,(
% 3.16/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f30])).
% 3.16/0.98  
% 3.16/0.98  fof(f84,plain,(
% 3.16/0.98    v2_pre_topc(sK0)),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f14,axiom,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f39,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.16/0.98    inference(ennf_transformation,[],[f14])).
% 3.16/0.98  
% 3.16/0.98  fof(f40,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.16/0.98    inference(flattening,[],[f39])).
% 3.16/0.98  
% 3.16/0.98  fof(f52,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.16/0.98    inference(nnf_transformation,[],[f40])).
% 3.16/0.98  
% 3.16/0.98  fof(f78,plain,(
% 3.16/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f52])).
% 3.16/0.98  
% 3.16/0.98  fof(f99,plain,(
% 3.16/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.16/0.98    inference(equality_resolution,[],[f78])).
% 3.16/0.98  
% 3.16/0.98  fof(f95,plain,(
% 3.16/0.98    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.16/0.98    inference(cnf_transformation,[],[f58])).
% 3.16/0.98  
% 3.16/0.98  fof(f60,plain,(
% 3.16/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.16/0.98    inference(cnf_transformation,[],[f49])).
% 3.16/0.98  
% 3.16/0.98  fof(f96,plain,(
% 3.16/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.16/0.98    inference(equality_resolution,[],[f60])).
% 3.16/0.98  
% 3.16/0.98  fof(f2,axiom,(
% 3.16/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f21,plain,(
% 3.16/0.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.16/0.98    inference(ennf_transformation,[],[f2])).
% 3.16/0.98  
% 3.16/0.98  fof(f22,plain,(
% 3.16/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.16/0.98    inference(flattening,[],[f21])).
% 3.16/0.98  
% 3.16/0.98  fof(f62,plain,(
% 3.16/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f22])).
% 3.16/0.98  
% 3.16/0.98  cnf(c_21,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1557,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_26,negated_conjecture,
% 3.16/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.16/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1554,plain,
% 3.16/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_6,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | v1_partfun1(X0,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | v1_xboole_0(X2)
% 3.16/0.98      | ~ v1_funct_1(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_5,plain,
% 3.16/0.98      ( v4_relat_1(X0,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.16/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_9,plain,
% 3.16/0.98      ( ~ v1_partfun1(X0,X1)
% 3.16/0.98      | ~ v4_relat_1(X0,X1)
% 3.16/0.98      | ~ v1_relat_1(X0)
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_398,plain,
% 3.16/0.98      ( ~ v1_partfun1(X0,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ v1_relat_1(X0)
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | v1_relat_1(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_402,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ v1_partfun1(X0,X1)
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_398,c_9,c_5,c_4]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_403,plain,
% 3.16/0.98      ( ~ v1_partfun1(X0,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_402]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_459,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.16/0.98      | v1_xboole_0(X2)
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(resolution,[status(thm)],[c_6,c_403]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_463,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | v1_xboole_0(X2)
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_459,c_9,c_6,c_5,c_4]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_464,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | v1_xboole_0(X2)
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | k1_relat_1(X0) = X1 ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_463]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_28,negated_conjecture,
% 3.16/0.98      ( v1_funct_1(sK3) ),
% 3.16/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_597,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | v1_xboole_0(X2)
% 3.16/0.98      | k1_relat_1(X0) = X1
% 3.16/0.98      | sK3 != X0 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_464,c_28]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_598,plain,
% 3.16/0.98      ( ~ v1_funct_2(sK3,X0,X1)
% 3.16/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | v1_xboole_0(X1)
% 3.16/0.98      | k1_relat_1(sK3) = X0 ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_597]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1542,plain,
% 3.16/0.98      ( k1_relat_1(sK3) = X0
% 3.16/0.98      | v1_funct_2(sK3,X0,X1) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.16/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2063,plain,
% 3.16/0.98      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.16/0.98      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1554,c_1542]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_36,negated_conjecture,
% 3.16/0.98      ( ~ v2_struct_0(sK0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_37,plain,
% 3.16/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_34,negated_conjecture,
% 3.16/0.98      ( l1_pre_topc(sK0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_39,plain,
% 3.16/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_27,negated_conjecture,
% 3.16/0.98      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_46,plain,
% 3.16/0.98      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_12,plain,
% 3.16/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_14,plain,
% 3.16/0.98      ( v2_struct_0(X0)
% 3.16/0.98      | ~ l1_struct_0(X0)
% 3.16/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_380,plain,
% 3.16/0.98      ( v2_struct_0(X0)
% 3.16/0.98      | ~ l1_pre_topc(X0)
% 3.16/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.16/0.98      inference(resolution,[status(thm)],[c_12,c_14]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2001,plain,
% 3.16/0.98      ( v2_struct_0(sK0)
% 3.16/0.98      | ~ l1_pre_topc(sK0)
% 3.16/0.98      | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_380]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2002,plain,
% 3.16/0.98      ( v2_struct_0(sK0) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_2001]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2162,plain,
% 3.16/0.98      ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_2063,c_37,c_39,c_46,c_2002]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_17,plain,
% 3.16/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.16/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.16/0.98      | ~ l1_pre_topc(X0)
% 3.16/0.98      | ~ l1_pre_topc(X1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_13,plain,
% 3.16/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_198,plain,
% 3.16/0.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.16/0.98      | ~ m1_pre_topc(X0,X1)
% 3.16/0.98      | ~ l1_pre_topc(X1) ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_17,c_13]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_199,plain,
% 3.16/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.16/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.16/0.98      | ~ l1_pre_topc(X1) ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_198]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1544,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.16/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3133,plain,
% 3.16/0.98      ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2162,c_1544]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_31,negated_conjecture,
% 3.16/0.98      ( l1_pre_topc(sK1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_42,plain,
% 3.16/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3810,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_3133,c_42]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3811,plain,
% 3.16/0.98      ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_3810]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_25,negated_conjecture,
% 3.16/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2169,plain,
% 3.16/0.98      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_2162,c_25]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_15,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X1)
% 3.16/0.98      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.16/0.98      | ~ l1_pre_topc(X1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1558,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 3.16/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.16/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3248,plain,
% 3.16/0.98      ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK2) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2169,c_1558]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_29,negated_conjecture,
% 3.16/0.98      ( m1_pre_topc(sK2,sK1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1552,plain,
% 3.16/0.98      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1559,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.16/0.98      | l1_pre_topc(X1) != iProver_top
% 3.16/0.98      | l1_pre_topc(X0) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2589,plain,
% 3.16/0.98      ( l1_pre_topc(sK2) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1552,c_1559]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3571,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.16/0.98      | m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_3248,c_42,c_2589]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3572,plain,
% 3.16/0.98      ( m1_pre_topc(X0,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_3571]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3820,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_3811,c_3572]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3847,plain,
% 3.16/0.98      ( m1_pre_topc(sK1,sK2) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1557,c_3820]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_53,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_55,plain,
% 3.16/0.98      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_53]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3151,plain,
% 3.16/0.98      ( m1_pre_topc(sK1,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) = iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_3133]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3272,plain,
% 3.16/0.98      ( m1_pre_topc(sK1,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1))) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_3248]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4201,plain,
% 3.16/0.98      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_3847,c_42,c_55,c_2589,c_3151,c_3272]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_22,plain,
% 3.16/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.16/0.98      | ~ m1_pre_topc(X0,X2)
% 3.16/0.98      | ~ m1_pre_topc(X2,X1)
% 3.16/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.16/0.98      | ~ l1_pre_topc(X1)
% 3.16/0.98      | ~ v2_pre_topc(X1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1556,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.16/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.16/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.16/0.98      | l1_pre_topc(X1) != iProver_top
% 3.16/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4206,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 3.16/0.98      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_4201,c_1556]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4214,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 3.16/0.98      | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.16/0.98      inference(light_normalisation,[status(thm)],[c_4206,c_2162]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_32,negated_conjecture,
% 3.16/0.98      ( v2_pre_topc(sK1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_41,plain,
% 3.16/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_11,plain,
% 3.16/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.16/0.98      | ~ l1_pre_topc(X1)
% 3.16/0.98      | ~ v2_pre_topc(X1)
% 3.16/0.98      | v2_pre_topc(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1560,plain,
% 3.16/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.16/0.98      | l1_pre_topc(X1) != iProver_top
% 3.16/0.98      | v2_pre_topc(X1) != iProver_top
% 3.16/0.98      | v2_pre_topc(X0) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3282,plain,
% 3.16/0.98      ( l1_pre_topc(sK1) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK2) = iProver_top
% 3.16/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1552,c_1560]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4843,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 3.16/0.98      | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) = iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_4214,c_41,c_42,c_2589,c_3282]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3966,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 3.16/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1552,c_1556]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4412,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 3.16/0.98      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_3966,c_41,c_42]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4421,plain,
% 3.16/0.98      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.16/0.98      | r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2162,c_4412]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_44,plain,
% 3.16/0.98      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4540,plain,
% 3.16/0.98      ( r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_4421,c_42,c_44,c_55]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_0,plain,
% 3.16/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.16/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1564,plain,
% 3.16/0.98      ( X0 = X1
% 3.16/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.16/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4545,plain,
% 3.16/0.98      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 3.16/0.98      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_4540,c_1564]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_5079,plain,
% 3.16/0.98      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 3.16/0.98      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.16/0.98      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_4843,c_4545]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3848,plain,
% 3.16/0.98      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1552,c_3820]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_6791,plain,
% 3.16/0.98      ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_5079,c_42,c_55,c_2589,c_3151,c_3272,c_3848]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2166,plain,
% 3.16/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_2162,c_1554]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_20,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.16/0.98      | ~ m1_pre_topc(X3,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.16/0.98      | v2_struct_0(X1)
% 3.16/0.98      | v2_struct_0(X2)
% 3.16/0.98      | ~ l1_pre_topc(X1)
% 3.16/0.98      | ~ l1_pre_topc(X2)
% 3.16/0.98      | ~ v2_pre_topc(X1)
% 3.16/0.98      | ~ v2_pre_topc(X2)
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.16/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_615,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.16/0.98      | ~ m1_pre_topc(X3,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.16/0.98      | v2_struct_0(X1)
% 3.16/0.98      | v2_struct_0(X2)
% 3.16/0.98      | ~ l1_pre_topc(X1)
% 3.16/0.98      | ~ l1_pre_topc(X2)
% 3.16/0.98      | ~ v2_pre_topc(X1)
% 3.16/0.98      | ~ v2_pre_topc(X2)
% 3.16/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.16/0.98      | sK3 != X0 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_616,plain,
% 3.16/0.98      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 3.16/0.98      | ~ m1_pre_topc(X2,X0)
% 3.16/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.16/0.98      | v2_struct_0(X0)
% 3.16/0.98      | v2_struct_0(X1)
% 3.16/0.98      | ~ l1_pre_topc(X0)
% 3.16/0.98      | ~ l1_pre_topc(X1)
% 3.16/0.98      | ~ v2_pre_topc(X0)
% 3.16/0.98      | ~ v2_pre_topc(X1)
% 3.16/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_615]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1541,plain,
% 3.16/0.98      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 3.16/0.98      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.16/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.16/0.98      | v2_struct_0(X1) = iProver_top
% 3.16/0.98      | v2_struct_0(X0) = iProver_top
% 3.16/0.98      | l1_pre_topc(X1) != iProver_top
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top
% 3.16/0.98      | v2_pre_topc(X1) != iProver_top
% 3.16/0.98      | v2_pre_topc(X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2346,plain,
% 3.16/0.98      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
% 3.16/0.98      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 3.16/0.98      | m1_pre_topc(X1,sK1) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
% 3.16/0.98      | v2_struct_0(X0) = iProver_top
% 3.16/0.98      | v2_struct_0(sK1) = iProver_top
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.16/0.98      | v2_pre_topc(X0) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2162,c_1541]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2379,plain,
% 3.16/0.98      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
% 3.16/0.98      | m1_pre_topc(X1,sK1) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
% 3.16/0.98      | v2_struct_0(X0) = iProver_top
% 3.16/0.98      | v2_struct_0(sK1) = iProver_top
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top
% 3.16/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.16/0.98      | v2_pre_topc(X0) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.16/0.98      inference(light_normalisation,[status(thm)],[c_2346,c_2162]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_33,negated_conjecture,
% 3.16/0.98      ( ~ v2_struct_0(sK1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_40,plain,
% 3.16/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3042,plain,
% 3.16/0.98      ( v2_pre_topc(X0) != iProver_top
% 3.16/0.98      | v2_struct_0(X0) = iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
% 3.16/0.98      | m1_pre_topc(X1,sK1) != iProver_top
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
% 3.16/0.98      | k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_2379,c_40,c_41,c_42]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3043,plain,
% 3.16/0.98      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),sK3,u1_struct_0(X1)) = k2_tmap_1(sK1,X0,sK3,X1)
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
% 3.16/0.98      | m1_pre_topc(X1,sK1) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) != iProver_top
% 3.16/0.98      | v2_struct_0(X0) = iProver_top
% 3.16/0.98      | l1_pre_topc(X0) != iProver_top
% 3.16/0.98      | v2_pre_topc(X0) != iProver_top ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_3042]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3053,plain,
% 3.16/0.98      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | v2_struct_0(sK0) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2166,c_3043]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_10,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.16/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_651,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.16/0.98      | sK3 != X0 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_652,plain,
% 3.16/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_651]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1540,plain,
% 3.16/0.98      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1965,plain,
% 3.16/0.98      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1554,c_1540]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2165,plain,
% 3.16/0.98      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_2162,c_1965]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3069,plain,
% 3.16/0.98      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | v2_struct_0(sK0) = iProver_top
% 3.16/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.16/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_3053,c_2165]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_35,negated_conjecture,
% 3.16/0.98      ( v2_pre_topc(sK0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_38,plain,
% 3.16/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1772,plain,
% 3.16/0.98      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0))
% 3.16/0.98      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_598]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1027,plain,( X0 = X0 ),theory(equality) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1835,plain,
% 3.16/0.98      ( sK3 = sK3 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1929,plain,
% 3.16/0.98      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1035,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | v1_funct_2(X3,X4,X5)
% 3.16/0.98      | X5 != X2
% 3.16/0.98      | X3 != X0
% 3.16/0.98      | X4 != X1 ),
% 3.16/0.98      theory(equality) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1810,plain,
% 3.16/0.98      ( v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | X2 != u1_struct_0(sK0)
% 3.16/0.98      | X1 != u1_struct_0(sK1)
% 3.16/0.98      | X0 != sK3 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1859,plain,
% 3.16/0.98      ( v1_funct_2(sK3,X0,X1)
% 3.16/0.98      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | X1 != u1_struct_0(sK0)
% 3.16/0.98      | X0 != u1_struct_0(sK1)
% 3.16/0.98      | sK3 != sK3 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1810]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1928,plain,
% 3.16/0.98      ( v1_funct_2(sK3,X0,u1_struct_0(sK0))
% 3.16/0.98      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | X0 != u1_struct_0(sK1)
% 3.16/0.98      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.16/0.98      | sK3 != sK3 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1859]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2077,plain,
% 3.16/0.98      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
% 3.16/0.98      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.16/0.98      | k1_relat_1(sK3) != u1_struct_0(sK1)
% 3.16/0.98      | sK3 != sK3 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1928]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2078,plain,
% 3.16/0.98      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.16/0.98      | k1_relat_1(sK3) != u1_struct_0(sK1)
% 3.16/0.98      | sK3 != sK3
% 3.16/0.98      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4944,plain,
% 3.16/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.16/0.98      | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_3069,c_36,c_37,c_38,c_34,c_39,c_27,c_46,c_26,c_1772,
% 3.16/0.98                 c_1835,c_1929,c_2001,c_2078]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4945,plain,
% 3.16/0.98      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.16/0.98      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_4944]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4953,plain,
% 3.16/0.98      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1552,c_4945]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_18,plain,
% 3.16/0.98      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.16/0.98      | ~ v1_funct_2(X4,X2,X3)
% 3.16/0.98      | ~ v1_funct_2(X4,X0,X1)
% 3.16/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.16/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | v1_xboole_0(X1)
% 3.16/0.98      | v1_xboole_0(X3)
% 3.16/0.98      | ~ v1_funct_1(X4) ),
% 3.16/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_24,negated_conjecture,
% 3.16/0.98      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_493,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ v1_funct_2(X0,X3,X4)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.16/0.98      | v1_xboole_0(X4)
% 3.16/0.98      | v1_xboole_0(X2)
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 3.16/0.98      | u1_struct_0(sK2) != X1
% 3.16/0.98      | u1_struct_0(sK0) != X2
% 3.16/0.98      | u1_struct_0(sK0) != X4
% 3.16/0.98      | u1_struct_0(sK1) != X3
% 3.16/0.98      | sK3 != X0 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_494,plain,
% 3.16/0.98      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.16/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.16/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0))
% 3.16/0.98      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.16/0.98      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_493]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_663,plain,
% 3.16/0.98      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.16/0.98      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.16/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.16/0.98      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0))
% 3.16/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_494]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1539,plain,
% 3.16/0.98      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2168,plain,
% 3.16/0.98      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_2162,c_1539]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2900,plain,
% 3.16/0.98      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_2168,c_37,c_39,c_2002]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2901,plain,
% 3.16/0.98      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_2900]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4963,plain,
% 3.16/0.98      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.16/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.16/0.98      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_4953,c_2901]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_6794,plain,
% 3.16/0.98      ( k7_relat_1(sK3,k1_relat_1(sK3)) != sK3
% 3.16/0.98      | v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_6791,c_4963]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1561,plain,
% 3.16/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.16/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2492,plain,
% 3.16/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2166,c_1561]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1,plain,
% 3.16/0.98      ( r1_tarski(X0,X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1563,plain,
% 3.16/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3,plain,
% 3.16/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.16/0.98      | ~ v1_relat_1(X0)
% 3.16/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.16/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1562,plain,
% 3.16/0.98      ( k7_relat_1(X0,X1) = X0
% 3.16/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.16/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3157,plain,
% 3.16/0.98      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.16/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1563,c_1562]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4226,plain,
% 3.16/0.98      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2492,c_3157]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_6823,plain,
% 3.16/0.98      ( sK3 != sK3
% 3.16/0.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.16/0.98      inference(light_normalisation,[status(thm)],[c_6794,c_4226]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_6824,plain,
% 3.16/0.98      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 3.16/0.98      inference(equality_resolution_simp,[status(thm)],[c_6823]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(contradiction,plain,
% 3.16/0.98      ( $false ),
% 3.16/0.98      inference(minisat,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_6824,c_2166,c_2078,c_2001,c_1929,c_1835,c_1772,c_26,
% 3.16/0.98                 c_46,c_27,c_34,c_36]) ).
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  ------                               Statistics
% 3.16/0.98  
% 3.16/0.98  ------ General
% 3.16/0.98  
% 3.16/0.98  abstr_ref_over_cycles:                  0
% 3.16/0.98  abstr_ref_under_cycles:                 0
% 3.16/0.98  gc_basic_clause_elim:                   0
% 3.16/0.98  forced_gc_time:                         0
% 3.16/0.98  parsing_time:                           0.01
% 3.16/0.98  unif_index_cands_time:                  0.
% 3.16/0.98  unif_index_add_time:                    0.
% 3.16/0.98  orderings_time:                         0.
% 3.16/0.98  out_proof_time:                         0.012
% 3.16/0.98  total_time:                             0.216
% 3.16/0.98  num_of_symbols:                         58
% 3.16/0.98  num_of_terms:                           3686
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing
% 3.16/0.98  
% 3.16/0.98  num_of_splits:                          0
% 3.16/0.98  num_of_split_atoms:                     0
% 3.16/0.98  num_of_reused_defs:                     0
% 3.16/0.98  num_eq_ax_congr_red:                    12
% 3.16/0.98  num_of_sem_filtered_clauses:            1
% 3.16/0.98  num_of_subtypes:                        0
% 3.16/0.98  monotx_restored_types:                  0
% 3.16/0.98  sat_num_of_epr_types:                   0
% 3.16/0.98  sat_num_of_non_cyclic_types:            0
% 3.16/0.98  sat_guarded_non_collapsed_types:        0
% 3.16/0.98  num_pure_diseq_elim:                    0
% 3.16/0.98  simp_replaced_by:                       0
% 3.16/0.98  res_preprocessed:                       154
% 3.16/0.98  prep_upred:                             0
% 3.16/0.98  prep_unflattend:                        21
% 3.16/0.98  smt_new_axioms:                         0
% 3.16/0.98  pred_elim_cands:                        9
% 3.16/0.98  pred_elim:                              5
% 3.16/0.98  pred_elim_cl:                           7
% 3.16/0.98  pred_elim_cycles:                       10
% 3.16/0.98  merged_defs:                            0
% 3.16/0.98  merged_defs_ncl:                        0
% 3.16/0.98  bin_hyper_res:                          0
% 3.16/0.98  prep_cycles:                            4
% 3.16/0.98  pred_elim_time:                         0.013
% 3.16/0.98  splitting_time:                         0.
% 3.16/0.98  sem_filter_time:                        0.
% 3.16/0.98  monotx_time:                            0.
% 3.16/0.98  subtype_inf_time:                       0.
% 3.16/0.98  
% 3.16/0.98  ------ Problem properties
% 3.16/0.98  
% 3.16/0.98  clauses:                                27
% 3.16/0.98  conjectures:                            11
% 3.16/0.98  epr:                                    13
% 3.16/0.98  horn:                                   25
% 3.16/0.98  ground:                                 12
% 3.16/0.98  unary:                                  12
% 3.16/0.98  binary:                                 3
% 3.16/0.98  lits:                                   72
% 3.16/0.98  lits_eq:                                7
% 3.16/0.98  fd_pure:                                0
% 3.16/0.98  fd_pseudo:                              0
% 3.16/0.98  fd_cond:                                1
% 3.16/0.98  fd_pseudo_cond:                         1
% 3.16/0.98  ac_symbols:                             0
% 3.16/0.98  
% 3.16/0.98  ------ Propositional Solver
% 3.16/0.98  
% 3.16/0.98  prop_solver_calls:                      30
% 3.16/0.98  prop_fast_solver_calls:                 1314
% 3.16/0.98  smt_solver_calls:                       0
% 3.16/0.98  smt_fast_solver_calls:                  0
% 3.16/0.98  prop_num_of_clauses:                    2026
% 3.16/0.98  prop_preprocess_simplified:             6633
% 3.16/0.98  prop_fo_subsumed:                       52
% 3.16/0.98  prop_solver_time:                       0.
% 3.16/0.98  smt_solver_time:                        0.
% 3.16/0.98  smt_fast_solver_time:                   0.
% 3.16/0.98  prop_fast_solver_time:                  0.
% 3.16/0.98  prop_unsat_core_time:                   0.
% 3.16/0.98  
% 3.16/0.98  ------ QBF
% 3.16/0.98  
% 3.16/0.98  qbf_q_res:                              0
% 3.16/0.98  qbf_num_tautologies:                    0
% 3.16/0.98  qbf_prep_cycles:                        0
% 3.16/0.98  
% 3.16/0.98  ------ BMC1
% 3.16/0.98  
% 3.16/0.98  bmc1_current_bound:                     -1
% 3.16/0.98  bmc1_last_solved_bound:                 -1
% 3.16/0.98  bmc1_unsat_core_size:                   -1
% 3.16/0.98  bmc1_unsat_core_parents_size:           -1
% 3.16/0.98  bmc1_merge_next_fun:                    0
% 3.16/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.98  
% 3.16/0.98  ------ Instantiation
% 3.16/0.98  
% 3.16/0.98  inst_num_of_clauses:                    654
% 3.16/0.98  inst_num_in_passive:                    250
% 3.16/0.98  inst_num_in_active:                     393
% 3.16/0.98  inst_num_in_unprocessed:                12
% 3.16/0.98  inst_num_of_loops:                      410
% 3.16/0.98  inst_num_of_learning_restarts:          0
% 3.16/0.98  inst_num_moves_active_passive:          11
% 3.16/0.98  inst_lit_activity:                      0
% 3.16/0.98  inst_lit_activity_moves:                0
% 3.16/0.98  inst_num_tautologies:                   0
% 3.16/0.98  inst_num_prop_implied:                  0
% 3.16/0.98  inst_num_existing_simplified:           0
% 3.16/0.98  inst_num_eq_res_simplified:             0
% 3.16/0.98  inst_num_child_elim:                    0
% 3.16/0.98  inst_num_of_dismatching_blockings:      153
% 3.16/0.98  inst_num_of_non_proper_insts:           932
% 3.16/0.98  inst_num_of_duplicates:                 0
% 3.16/0.98  inst_inst_num_from_inst_to_res:         0
% 3.16/0.98  inst_dismatching_checking_time:         0.
% 3.16/0.98  
% 3.16/0.98  ------ Resolution
% 3.16/0.98  
% 3.16/0.98  res_num_of_clauses:                     0
% 3.16/0.98  res_num_in_passive:                     0
% 3.16/0.98  res_num_in_active:                      0
% 3.16/0.98  res_num_of_loops:                       158
% 3.16/0.98  res_forward_subset_subsumed:            199
% 3.16/0.98  res_backward_subset_subsumed:           2
% 3.16/0.98  res_forward_subsumed:                   0
% 3.16/0.98  res_backward_subsumed:                  0
% 3.16/0.98  res_forward_subsumption_resolution:     1
% 3.16/0.98  res_backward_subsumption_resolution:    0
% 3.16/0.98  res_clause_to_clause_subsumption:       410
% 3.16/0.98  res_orphan_elimination:                 0
% 3.16/0.98  res_tautology_del:                      86
% 3.16/0.98  res_num_eq_res_simplified:              0
% 3.16/0.98  res_num_sel_changes:                    0
% 3.16/0.98  res_moves_from_active_to_pass:          0
% 3.16/0.98  
% 3.16/0.98  ------ Superposition
% 3.16/0.98  
% 3.16/0.98  sup_time_total:                         0.
% 3.16/0.98  sup_time_generating:                    0.
% 3.16/0.98  sup_time_sim_full:                      0.
% 3.16/0.98  sup_time_sim_immed:                     0.
% 3.16/0.98  
% 3.16/0.98  sup_num_of_clauses:                     96
% 3.16/0.98  sup_num_in_active:                      66
% 3.16/0.98  sup_num_in_passive:                     30
% 3.16/0.98  sup_num_of_loops:                       80
% 3.16/0.98  sup_fw_superposition:                   80
% 3.16/0.98  sup_bw_superposition:                   51
% 3.16/0.98  sup_immediate_simplified:               42
% 3.16/0.98  sup_given_eliminated:                   0
% 3.16/0.98  comparisons_done:                       0
% 3.16/0.98  comparisons_avoided:                    0
% 3.16/0.98  
% 3.16/0.98  ------ Simplifications
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  sim_fw_subset_subsumed:                 15
% 3.16/0.98  sim_bw_subset_subsumed:                 3
% 3.16/0.98  sim_fw_subsumed:                        11
% 3.16/0.98  sim_bw_subsumed:                        1
% 3.16/0.98  sim_fw_subsumption_res:                 0
% 3.16/0.98  sim_bw_subsumption_res:                 0
% 3.16/0.98  sim_tautology_del:                      16
% 3.16/0.98  sim_eq_tautology_del:                   4
% 3.16/0.98  sim_eq_res_simp:                        1
% 3.16/0.98  sim_fw_demodulated:                     1
% 3.16/0.98  sim_bw_demodulated:                     13
% 3.16/0.98  sim_light_normalised:                   18
% 3.16/0.98  sim_joinable_taut:                      0
% 3.16/0.98  sim_joinable_simp:                      0
% 3.16/0.98  sim_ac_normalised:                      0
% 3.16/0.98  sim_smt_subsumption:                    0
% 3.16/0.98  
%------------------------------------------------------------------------------
