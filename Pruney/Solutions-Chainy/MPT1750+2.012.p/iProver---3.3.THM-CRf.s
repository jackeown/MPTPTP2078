%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:24 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  163 (1874 expanded)
%              Number of clauses        :   92 ( 486 expanded)
%              Number of leaves         :   19 ( 562 expanded)
%              Depth                    :   24
%              Number of atoms          :  650 (14895 expanded)
%              Number of equality atoms :  165 (1708 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f44,f43,f42,f41])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1138,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_336,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_9,c_5,c_4])).

cnf(c_341,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_436,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_341])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_9,c_6,c_5,c_4])).

cnf(c_441,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_318,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_583,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_318,c_28])).

cnf(c_584,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_586,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_30])).

cnf(c_631,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK0) != X2
    | k1_relat_1(X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_441,c_586])).

cnf(c_632,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_1128,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1528,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1128])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1876,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_39,c_40])).

cnf(c_19,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1884,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_1876,c_19])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1139,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2337,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1139])).

cnf(c_2515,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK3)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2337])).

cnf(c_12,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_576,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_577,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_1133,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1881,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1876,c_1133])).

cnf(c_2741,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2515,c_1881])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_469,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_473,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_27,c_26,c_25])).

cnf(c_474,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_531,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_474,c_29])).

cnf(c_532,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_30,c_28])).

cnf(c_1134,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2)
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1385,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1134])).

cnf(c_1287,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1388,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1385,c_22,c_21,c_20,c_1287])).

cnf(c_1879,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1876,c_1388])).

cnf(c_2747,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_2741,c_1879])).

cnf(c_1142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1628,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1142])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1144,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1143,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1715,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_1143])).

cnf(c_2940,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1628,c_1715])).

cnf(c_1882,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1876,c_1138])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1141,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2506,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_1141])).

cnf(c_3026,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_39])).

cnf(c_3343,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_2747,c_2940,c_3026])).

cnf(c_16,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_18,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_397,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != X3
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK0) != X2
    | u1_struct_0(sK0) != X5
    | u1_struct_0(sK1) != X4
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_606,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_586,c_398])).

cnf(c_792,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sP0_iProver_split
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_606])).

cnf(c_1130,plain,
    ( sK3 != k2_tmap_1(sK1,sK0,sK3,sK2)
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_2930,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1130,c_1876])).

cnf(c_3345,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3343,c_2930])).

cnf(c_791,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_606])).

cnf(c_1131,plain,
    ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_3214,plain,
    ( v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1131,c_2741])).

cnf(c_3222,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_3214])).

cnf(c_1137,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1883,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1876,c_1137])).

cnf(c_794,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1375,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3345,c_3222,c_1883,c_1882,c_1375,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 2.23/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.01  
% 2.23/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.23/1.01  
% 2.23/1.01  ------  iProver source info
% 2.23/1.01  
% 2.23/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.23/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.23/1.01  git: non_committed_changes: false
% 2.23/1.01  git: last_make_outside_of_git: false
% 2.23/1.01  
% 2.23/1.01  ------ 
% 2.23/1.01  
% 2.23/1.01  ------ Input Options
% 2.23/1.01  
% 2.23/1.01  --out_options                           all
% 2.23/1.01  --tptp_safe_out                         true
% 2.23/1.01  --problem_path                          ""
% 2.23/1.01  --include_path                          ""
% 2.23/1.01  --clausifier                            res/vclausify_rel
% 2.23/1.01  --clausifier_options                    --mode clausify
% 2.23/1.01  --stdin                                 false
% 2.23/1.01  --stats_out                             all
% 2.23/1.01  
% 2.23/1.01  ------ General Options
% 2.23/1.01  
% 2.23/1.01  --fof                                   false
% 2.23/1.01  --time_out_real                         305.
% 2.23/1.01  --time_out_virtual                      -1.
% 2.23/1.01  --symbol_type_check                     false
% 2.23/1.01  --clausify_out                          false
% 2.23/1.01  --sig_cnt_out                           false
% 2.23/1.01  --trig_cnt_out                          false
% 2.23/1.01  --trig_cnt_out_tolerance                1.
% 2.23/1.01  --trig_cnt_out_sk_spl                   false
% 2.23/1.01  --abstr_cl_out                          false
% 2.23/1.01  
% 2.23/1.01  ------ Global Options
% 2.23/1.01  
% 2.23/1.01  --schedule                              default
% 2.23/1.01  --add_important_lit                     false
% 2.23/1.01  --prop_solver_per_cl                    1000
% 2.23/1.01  --min_unsat_core                        false
% 2.23/1.01  --soft_assumptions                      false
% 2.23/1.01  --soft_lemma_size                       3
% 2.23/1.01  --prop_impl_unit_size                   0
% 2.23/1.01  --prop_impl_unit                        []
% 2.23/1.01  --share_sel_clauses                     true
% 2.23/1.01  --reset_solvers                         false
% 2.23/1.01  --bc_imp_inh                            [conj_cone]
% 2.23/1.01  --conj_cone_tolerance                   3.
% 2.23/1.01  --extra_neg_conj                        none
% 2.23/1.01  --large_theory_mode                     true
% 2.23/1.01  --prolific_symb_bound                   200
% 2.23/1.01  --lt_threshold                          2000
% 2.23/1.01  --clause_weak_htbl                      true
% 2.23/1.01  --gc_record_bc_elim                     false
% 2.23/1.01  
% 2.23/1.01  ------ Preprocessing Options
% 2.23/1.01  
% 2.23/1.01  --preprocessing_flag                    true
% 2.23/1.01  --time_out_prep_mult                    0.1
% 2.23/1.01  --splitting_mode                        input
% 2.23/1.01  --splitting_grd                         true
% 2.23/1.01  --splitting_cvd                         false
% 2.23/1.01  --splitting_cvd_svl                     false
% 2.23/1.01  --splitting_nvd                         32
% 2.23/1.01  --sub_typing                            true
% 2.23/1.01  --prep_gs_sim                           true
% 2.23/1.01  --prep_unflatten                        true
% 2.23/1.01  --prep_res_sim                          true
% 2.23/1.01  --prep_upred                            true
% 2.23/1.01  --prep_sem_filter                       exhaustive
% 2.23/1.01  --prep_sem_filter_out                   false
% 2.23/1.01  --pred_elim                             true
% 2.23/1.01  --res_sim_input                         true
% 2.23/1.01  --eq_ax_congr_red                       true
% 2.23/1.01  --pure_diseq_elim                       true
% 2.23/1.01  --brand_transform                       false
% 2.23/1.01  --non_eq_to_eq                          false
% 2.23/1.01  --prep_def_merge                        true
% 2.23/1.01  --prep_def_merge_prop_impl              false
% 2.23/1.01  --prep_def_merge_mbd                    true
% 2.23/1.01  --prep_def_merge_tr_red                 false
% 2.23/1.01  --prep_def_merge_tr_cl                  false
% 2.23/1.01  --smt_preprocessing                     true
% 2.23/1.01  --smt_ac_axioms                         fast
% 2.23/1.01  --preprocessed_out                      false
% 2.23/1.01  --preprocessed_stats                    false
% 2.23/1.01  
% 2.23/1.01  ------ Abstraction refinement Options
% 2.23/1.01  
% 2.23/1.01  --abstr_ref                             []
% 2.23/1.01  --abstr_ref_prep                        false
% 2.23/1.01  --abstr_ref_until_sat                   false
% 2.23/1.01  --abstr_ref_sig_restrict                funpre
% 2.23/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/1.01  --abstr_ref_under                       []
% 2.23/1.01  
% 2.23/1.01  ------ SAT Options
% 2.23/1.01  
% 2.23/1.01  --sat_mode                              false
% 2.23/1.01  --sat_fm_restart_options                ""
% 2.23/1.01  --sat_gr_def                            false
% 2.23/1.01  --sat_epr_types                         true
% 2.23/1.01  --sat_non_cyclic_types                  false
% 2.23/1.01  --sat_finite_models                     false
% 2.23/1.01  --sat_fm_lemmas                         false
% 2.23/1.01  --sat_fm_prep                           false
% 2.23/1.01  --sat_fm_uc_incr                        true
% 2.23/1.01  --sat_out_model                         small
% 2.23/1.01  --sat_out_clauses                       false
% 2.23/1.01  
% 2.23/1.01  ------ QBF Options
% 2.23/1.01  
% 2.23/1.01  --qbf_mode                              false
% 2.23/1.01  --qbf_elim_univ                         false
% 2.23/1.01  --qbf_dom_inst                          none
% 2.23/1.01  --qbf_dom_pre_inst                      false
% 2.23/1.01  --qbf_sk_in                             false
% 2.23/1.01  --qbf_pred_elim                         true
% 2.23/1.01  --qbf_split                             512
% 2.23/1.01  
% 2.23/1.01  ------ BMC1 Options
% 2.23/1.01  
% 2.23/1.01  --bmc1_incremental                      false
% 2.23/1.01  --bmc1_axioms                           reachable_all
% 2.23/1.01  --bmc1_min_bound                        0
% 2.23/1.01  --bmc1_max_bound                        -1
% 2.23/1.01  --bmc1_max_bound_default                -1
% 2.23/1.01  --bmc1_symbol_reachability              true
% 2.23/1.01  --bmc1_property_lemmas                  false
% 2.23/1.01  --bmc1_k_induction                      false
% 2.23/1.01  --bmc1_non_equiv_states                 false
% 2.23/1.01  --bmc1_deadlock                         false
% 2.23/1.01  --bmc1_ucm                              false
% 2.23/1.01  --bmc1_add_unsat_core                   none
% 2.23/1.01  --bmc1_unsat_core_children              false
% 2.23/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/1.01  --bmc1_out_stat                         full
% 2.23/1.01  --bmc1_ground_init                      false
% 2.23/1.01  --bmc1_pre_inst_next_state              false
% 2.23/1.01  --bmc1_pre_inst_state                   false
% 2.23/1.01  --bmc1_pre_inst_reach_state             false
% 2.23/1.01  --bmc1_out_unsat_core                   false
% 2.23/1.01  --bmc1_aig_witness_out                  false
% 2.23/1.01  --bmc1_verbose                          false
% 2.23/1.01  --bmc1_dump_clauses_tptp                false
% 2.23/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.23/1.01  --bmc1_dump_file                        -
% 2.23/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.23/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.23/1.01  --bmc1_ucm_extend_mode                  1
% 2.23/1.01  --bmc1_ucm_init_mode                    2
% 2.23/1.01  --bmc1_ucm_cone_mode                    none
% 2.23/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.23/1.01  --bmc1_ucm_relax_model                  4
% 2.23/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.23/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/1.01  --bmc1_ucm_layered_model                none
% 2.23/1.01  --bmc1_ucm_max_lemma_size               10
% 2.23/1.01  
% 2.23/1.01  ------ AIG Options
% 2.23/1.01  
% 2.23/1.01  --aig_mode                              false
% 2.23/1.01  
% 2.23/1.01  ------ Instantiation Options
% 2.23/1.01  
% 2.23/1.01  --instantiation_flag                    true
% 2.23/1.01  --inst_sos_flag                         false
% 2.23/1.01  --inst_sos_phase                        true
% 2.23/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/1.01  --inst_lit_sel_side                     num_symb
% 2.23/1.01  --inst_solver_per_active                1400
% 2.23/1.01  --inst_solver_calls_frac                1.
% 2.23/1.01  --inst_passive_queue_type               priority_queues
% 2.23/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/1.01  --inst_passive_queues_freq              [25;2]
% 2.23/1.01  --inst_dismatching                      true
% 2.23/1.01  --inst_eager_unprocessed_to_passive     true
% 2.23/1.01  --inst_prop_sim_given                   true
% 2.23/1.01  --inst_prop_sim_new                     false
% 2.23/1.01  --inst_subs_new                         false
% 2.23/1.01  --inst_eq_res_simp                      false
% 2.23/1.01  --inst_subs_given                       false
% 2.23/1.01  --inst_orphan_elimination               true
% 2.23/1.01  --inst_learning_loop_flag               true
% 2.23/1.01  --inst_learning_start                   3000
% 2.23/1.01  --inst_learning_factor                  2
% 2.23/1.01  --inst_start_prop_sim_after_learn       3
% 2.23/1.01  --inst_sel_renew                        solver
% 2.23/1.01  --inst_lit_activity_flag                true
% 2.23/1.01  --inst_restr_to_given                   false
% 2.23/1.01  --inst_activity_threshold               500
% 2.23/1.01  --inst_out_proof                        true
% 2.23/1.01  
% 2.23/1.01  ------ Resolution Options
% 2.23/1.01  
% 2.23/1.01  --resolution_flag                       true
% 2.23/1.01  --res_lit_sel                           adaptive
% 2.23/1.01  --res_lit_sel_side                      none
% 2.23/1.01  --res_ordering                          kbo
% 2.23/1.01  --res_to_prop_solver                    active
% 2.23/1.01  --res_prop_simpl_new                    false
% 2.23/1.01  --res_prop_simpl_given                  true
% 2.23/1.01  --res_passive_queue_type                priority_queues
% 2.23/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/1.01  --res_passive_queues_freq               [15;5]
% 2.23/1.01  --res_forward_subs                      full
% 2.23/1.01  --res_backward_subs                     full
% 2.23/1.01  --res_forward_subs_resolution           true
% 2.23/1.01  --res_backward_subs_resolution          true
% 2.23/1.01  --res_orphan_elimination                true
% 2.23/1.01  --res_time_limit                        2.
% 2.23/1.01  --res_out_proof                         true
% 2.23/1.01  
% 2.23/1.01  ------ Superposition Options
% 2.23/1.01  
% 2.23/1.01  --superposition_flag                    true
% 2.23/1.01  --sup_passive_queue_type                priority_queues
% 2.23/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.23/1.01  --demod_completeness_check              fast
% 2.23/1.01  --demod_use_ground                      true
% 2.23/1.01  --sup_to_prop_solver                    passive
% 2.23/1.01  --sup_prop_simpl_new                    true
% 2.23/1.01  --sup_prop_simpl_given                  true
% 2.23/1.01  --sup_fun_splitting                     false
% 2.23/1.01  --sup_smt_interval                      50000
% 2.23/1.01  
% 2.23/1.01  ------ Superposition Simplification Setup
% 2.23/1.01  
% 2.23/1.01  --sup_indices_passive                   []
% 2.23/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.01  --sup_full_bw                           [BwDemod]
% 2.23/1.01  --sup_immed_triv                        [TrivRules]
% 2.23/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.01  --sup_immed_bw_main                     []
% 2.23/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.01  
% 2.23/1.01  ------ Combination Options
% 2.23/1.01  
% 2.23/1.01  --comb_res_mult                         3
% 2.23/1.01  --comb_sup_mult                         2
% 2.23/1.01  --comb_inst_mult                        10
% 2.23/1.01  
% 2.23/1.01  ------ Debug Options
% 2.23/1.01  
% 2.23/1.01  --dbg_backtrace                         false
% 2.23/1.01  --dbg_dump_prop_clauses                 false
% 2.23/1.01  --dbg_dump_prop_clauses_file            -
% 2.23/1.01  --dbg_out_stat                          false
% 2.23/1.01  ------ Parsing...
% 2.23/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.23/1.01  
% 2.23/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.23/1.01  
% 2.23/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.23/1.01  
% 2.23/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.23/1.01  ------ Proving...
% 2.23/1.01  ------ Problem Properties 
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  clauses                                 19
% 2.23/1.01  conjectures                             4
% 2.23/1.01  EPR                                     3
% 2.23/1.01  Horn                                    19
% 2.23/1.01  unary                                   7
% 2.23/1.01  binary                                  1
% 2.23/1.01  lits                                    49
% 2.23/1.01  lits eq                                 13
% 2.23/1.01  fd_pure                                 0
% 2.23/1.01  fd_pseudo                               0
% 2.23/1.01  fd_cond                                 0
% 2.23/1.01  fd_pseudo_cond                          5
% 2.23/1.01  AC symbols                              0
% 2.23/1.01  
% 2.23/1.01  ------ Schedule dynamic 5 is on 
% 2.23/1.01  
% 2.23/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  ------ 
% 2.23/1.01  Current options:
% 2.23/1.01  ------ 
% 2.23/1.01  
% 2.23/1.01  ------ Input Options
% 2.23/1.01  
% 2.23/1.01  --out_options                           all
% 2.23/1.01  --tptp_safe_out                         true
% 2.23/1.01  --problem_path                          ""
% 2.23/1.01  --include_path                          ""
% 2.23/1.01  --clausifier                            res/vclausify_rel
% 2.23/1.01  --clausifier_options                    --mode clausify
% 2.23/1.01  --stdin                                 false
% 2.23/1.01  --stats_out                             all
% 2.23/1.01  
% 2.23/1.01  ------ General Options
% 2.23/1.01  
% 2.23/1.01  --fof                                   false
% 2.23/1.01  --time_out_real                         305.
% 2.23/1.01  --time_out_virtual                      -1.
% 2.23/1.01  --symbol_type_check                     false
% 2.23/1.01  --clausify_out                          false
% 2.23/1.01  --sig_cnt_out                           false
% 2.23/1.01  --trig_cnt_out                          false
% 2.23/1.01  --trig_cnt_out_tolerance                1.
% 2.23/1.01  --trig_cnt_out_sk_spl                   false
% 2.23/1.01  --abstr_cl_out                          false
% 2.23/1.01  
% 2.23/1.01  ------ Global Options
% 2.23/1.01  
% 2.23/1.01  --schedule                              default
% 2.23/1.01  --add_important_lit                     false
% 2.23/1.01  --prop_solver_per_cl                    1000
% 2.23/1.01  --min_unsat_core                        false
% 2.23/1.01  --soft_assumptions                      false
% 2.23/1.01  --soft_lemma_size                       3
% 2.23/1.01  --prop_impl_unit_size                   0
% 2.23/1.01  --prop_impl_unit                        []
% 2.23/1.01  --share_sel_clauses                     true
% 2.23/1.01  --reset_solvers                         false
% 2.23/1.01  --bc_imp_inh                            [conj_cone]
% 2.23/1.01  --conj_cone_tolerance                   3.
% 2.23/1.01  --extra_neg_conj                        none
% 2.23/1.01  --large_theory_mode                     true
% 2.23/1.01  --prolific_symb_bound                   200
% 2.23/1.01  --lt_threshold                          2000
% 2.23/1.01  --clause_weak_htbl                      true
% 2.23/1.01  --gc_record_bc_elim                     false
% 2.23/1.01  
% 2.23/1.01  ------ Preprocessing Options
% 2.23/1.01  
% 2.23/1.01  --preprocessing_flag                    true
% 2.23/1.01  --time_out_prep_mult                    0.1
% 2.23/1.01  --splitting_mode                        input
% 2.23/1.01  --splitting_grd                         true
% 2.23/1.01  --splitting_cvd                         false
% 2.23/1.01  --splitting_cvd_svl                     false
% 2.23/1.01  --splitting_nvd                         32
% 2.23/1.01  --sub_typing                            true
% 2.23/1.01  --prep_gs_sim                           true
% 2.23/1.01  --prep_unflatten                        true
% 2.23/1.01  --prep_res_sim                          true
% 2.23/1.01  --prep_upred                            true
% 2.23/1.01  --prep_sem_filter                       exhaustive
% 2.23/1.01  --prep_sem_filter_out                   false
% 2.23/1.01  --pred_elim                             true
% 2.23/1.01  --res_sim_input                         true
% 2.23/1.01  --eq_ax_congr_red                       true
% 2.23/1.01  --pure_diseq_elim                       true
% 2.23/1.01  --brand_transform                       false
% 2.23/1.01  --non_eq_to_eq                          false
% 2.23/1.01  --prep_def_merge                        true
% 2.23/1.01  --prep_def_merge_prop_impl              false
% 2.23/1.01  --prep_def_merge_mbd                    true
% 2.23/1.01  --prep_def_merge_tr_red                 false
% 2.23/1.01  --prep_def_merge_tr_cl                  false
% 2.23/1.01  --smt_preprocessing                     true
% 2.23/1.01  --smt_ac_axioms                         fast
% 2.23/1.01  --preprocessed_out                      false
% 2.23/1.01  --preprocessed_stats                    false
% 2.23/1.01  
% 2.23/1.01  ------ Abstraction refinement Options
% 2.23/1.01  
% 2.23/1.01  --abstr_ref                             []
% 2.23/1.01  --abstr_ref_prep                        false
% 2.23/1.01  --abstr_ref_until_sat                   false
% 2.23/1.01  --abstr_ref_sig_restrict                funpre
% 2.23/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/1.01  --abstr_ref_under                       []
% 2.23/1.01  
% 2.23/1.01  ------ SAT Options
% 2.23/1.01  
% 2.23/1.01  --sat_mode                              false
% 2.23/1.01  --sat_fm_restart_options                ""
% 2.23/1.01  --sat_gr_def                            false
% 2.23/1.01  --sat_epr_types                         true
% 2.23/1.01  --sat_non_cyclic_types                  false
% 2.23/1.01  --sat_finite_models                     false
% 2.23/1.01  --sat_fm_lemmas                         false
% 2.23/1.01  --sat_fm_prep                           false
% 2.23/1.01  --sat_fm_uc_incr                        true
% 2.23/1.01  --sat_out_model                         small
% 2.23/1.01  --sat_out_clauses                       false
% 2.23/1.01  
% 2.23/1.01  ------ QBF Options
% 2.23/1.01  
% 2.23/1.01  --qbf_mode                              false
% 2.23/1.01  --qbf_elim_univ                         false
% 2.23/1.01  --qbf_dom_inst                          none
% 2.23/1.01  --qbf_dom_pre_inst                      false
% 2.23/1.01  --qbf_sk_in                             false
% 2.23/1.01  --qbf_pred_elim                         true
% 2.23/1.01  --qbf_split                             512
% 2.23/1.01  
% 2.23/1.01  ------ BMC1 Options
% 2.23/1.01  
% 2.23/1.01  --bmc1_incremental                      false
% 2.23/1.01  --bmc1_axioms                           reachable_all
% 2.23/1.01  --bmc1_min_bound                        0
% 2.23/1.01  --bmc1_max_bound                        -1
% 2.23/1.01  --bmc1_max_bound_default                -1
% 2.23/1.01  --bmc1_symbol_reachability              true
% 2.23/1.01  --bmc1_property_lemmas                  false
% 2.23/1.01  --bmc1_k_induction                      false
% 2.23/1.01  --bmc1_non_equiv_states                 false
% 2.23/1.01  --bmc1_deadlock                         false
% 2.23/1.01  --bmc1_ucm                              false
% 2.23/1.01  --bmc1_add_unsat_core                   none
% 2.23/1.01  --bmc1_unsat_core_children              false
% 2.23/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/1.01  --bmc1_out_stat                         full
% 2.23/1.01  --bmc1_ground_init                      false
% 2.23/1.01  --bmc1_pre_inst_next_state              false
% 2.23/1.01  --bmc1_pre_inst_state                   false
% 2.23/1.01  --bmc1_pre_inst_reach_state             false
% 2.23/1.01  --bmc1_out_unsat_core                   false
% 2.23/1.01  --bmc1_aig_witness_out                  false
% 2.23/1.01  --bmc1_verbose                          false
% 2.23/1.01  --bmc1_dump_clauses_tptp                false
% 2.23/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.23/1.01  --bmc1_dump_file                        -
% 2.23/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.23/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.23/1.01  --bmc1_ucm_extend_mode                  1
% 2.23/1.01  --bmc1_ucm_init_mode                    2
% 2.23/1.01  --bmc1_ucm_cone_mode                    none
% 2.23/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.23/1.01  --bmc1_ucm_relax_model                  4
% 2.23/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.23/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/1.01  --bmc1_ucm_layered_model                none
% 2.23/1.01  --bmc1_ucm_max_lemma_size               10
% 2.23/1.01  
% 2.23/1.01  ------ AIG Options
% 2.23/1.01  
% 2.23/1.01  --aig_mode                              false
% 2.23/1.01  
% 2.23/1.01  ------ Instantiation Options
% 2.23/1.01  
% 2.23/1.01  --instantiation_flag                    true
% 2.23/1.01  --inst_sos_flag                         false
% 2.23/1.01  --inst_sos_phase                        true
% 2.23/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/1.01  --inst_lit_sel_side                     none
% 2.23/1.01  --inst_solver_per_active                1400
% 2.23/1.01  --inst_solver_calls_frac                1.
% 2.23/1.01  --inst_passive_queue_type               priority_queues
% 2.23/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/1.01  --inst_passive_queues_freq              [25;2]
% 2.23/1.01  --inst_dismatching                      true
% 2.23/1.01  --inst_eager_unprocessed_to_passive     true
% 2.23/1.01  --inst_prop_sim_given                   true
% 2.23/1.01  --inst_prop_sim_new                     false
% 2.23/1.01  --inst_subs_new                         false
% 2.23/1.01  --inst_eq_res_simp                      false
% 2.23/1.01  --inst_subs_given                       false
% 2.23/1.01  --inst_orphan_elimination               true
% 2.23/1.01  --inst_learning_loop_flag               true
% 2.23/1.01  --inst_learning_start                   3000
% 2.23/1.01  --inst_learning_factor                  2
% 2.23/1.01  --inst_start_prop_sim_after_learn       3
% 2.23/1.01  --inst_sel_renew                        solver
% 2.23/1.01  --inst_lit_activity_flag                true
% 2.23/1.01  --inst_restr_to_given                   false
% 2.23/1.01  --inst_activity_threshold               500
% 2.23/1.01  --inst_out_proof                        true
% 2.23/1.01  
% 2.23/1.01  ------ Resolution Options
% 2.23/1.01  
% 2.23/1.01  --resolution_flag                       false
% 2.23/1.01  --res_lit_sel                           adaptive
% 2.23/1.01  --res_lit_sel_side                      none
% 2.23/1.01  --res_ordering                          kbo
% 2.23/1.01  --res_to_prop_solver                    active
% 2.23/1.01  --res_prop_simpl_new                    false
% 2.23/1.01  --res_prop_simpl_given                  true
% 2.23/1.01  --res_passive_queue_type                priority_queues
% 2.23/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/1.01  --res_passive_queues_freq               [15;5]
% 2.23/1.01  --res_forward_subs                      full
% 2.23/1.01  --res_backward_subs                     full
% 2.23/1.01  --res_forward_subs_resolution           true
% 2.23/1.01  --res_backward_subs_resolution          true
% 2.23/1.01  --res_orphan_elimination                true
% 2.23/1.01  --res_time_limit                        2.
% 2.23/1.01  --res_out_proof                         true
% 2.23/1.01  
% 2.23/1.01  ------ Superposition Options
% 2.23/1.01  
% 2.23/1.01  --superposition_flag                    true
% 2.23/1.01  --sup_passive_queue_type                priority_queues
% 2.23/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.23/1.01  --demod_completeness_check              fast
% 2.23/1.01  --demod_use_ground                      true
% 2.23/1.01  --sup_to_prop_solver                    passive
% 2.23/1.01  --sup_prop_simpl_new                    true
% 2.23/1.01  --sup_prop_simpl_given                  true
% 2.23/1.01  --sup_fun_splitting                     false
% 2.23/1.01  --sup_smt_interval                      50000
% 2.23/1.01  
% 2.23/1.01  ------ Superposition Simplification Setup
% 2.23/1.01  
% 2.23/1.01  --sup_indices_passive                   []
% 2.23/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.01  --sup_full_bw                           [BwDemod]
% 2.23/1.01  --sup_immed_triv                        [TrivRules]
% 2.23/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.01  --sup_immed_bw_main                     []
% 2.23/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/1.01  
% 2.23/1.01  ------ Combination Options
% 2.23/1.01  
% 2.23/1.01  --comb_res_mult                         3
% 2.23/1.01  --comb_sup_mult                         2
% 2.23/1.01  --comb_inst_mult                        10
% 2.23/1.01  
% 2.23/1.01  ------ Debug Options
% 2.23/1.01  
% 2.23/1.01  --dbg_backtrace                         false
% 2.23/1.01  --dbg_dump_prop_clauses                 false
% 2.23/1.01  --dbg_dump_prop_clauses_file            -
% 2.23/1.01  --dbg_out_stat                          false
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  ------ Proving...
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  % SZS status Theorem for theBenchmark.p
% 2.23/1.01  
% 2.23/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.23/1.01  
% 2.23/1.01  fof(f14,conjecture,(
% 2.23/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f15,negated_conjecture,(
% 2.23/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.23/1.01    inference(negated_conjecture,[],[f14])).
% 2.23/1.01  
% 2.23/1.01  fof(f36,plain,(
% 2.23/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.23/1.01    inference(ennf_transformation,[],[f15])).
% 2.23/1.01  
% 2.23/1.01  fof(f37,plain,(
% 2.23/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/1.01    inference(flattening,[],[f36])).
% 2.23/1.01  
% 2.23/1.01  fof(f44,plain,(
% 2.23/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.23/1.01    introduced(choice_axiom,[])).
% 2.23/1.01  
% 2.23/1.01  fof(f43,plain,(
% 2.23/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.23/1.01    introduced(choice_axiom,[])).
% 2.23/1.01  
% 2.23/1.01  fof(f42,plain,(
% 2.23/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.23/1.01    introduced(choice_axiom,[])).
% 2.23/1.01  
% 2.23/1.01  fof(f41,plain,(
% 2.23/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.23/1.01    introduced(choice_axiom,[])).
% 2.23/1.01  
% 2.23/1.01  fof(f45,plain,(
% 2.23/1.01    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f44,f43,f42,f41])).
% 2.23/1.01  
% 2.23/1.01  fof(f74,plain,(
% 2.23/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f5,axiom,(
% 2.23/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f21,plain,(
% 2.23/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.23/1.01    inference(ennf_transformation,[],[f5])).
% 2.23/1.01  
% 2.23/1.01  fof(f22,plain,(
% 2.23/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.23/1.01    inference(flattening,[],[f21])).
% 2.23/1.01  
% 2.23/1.01  fof(f53,plain,(
% 2.23/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f22])).
% 2.23/1.01  
% 2.23/1.01  fof(f4,axiom,(
% 2.23/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f16,plain,(
% 2.23/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.23/1.01    inference(pure_predicate_removal,[],[f4])).
% 2.23/1.01  
% 2.23/1.01  fof(f20,plain,(
% 2.23/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/1.01    inference(ennf_transformation,[],[f16])).
% 2.23/1.01  
% 2.23/1.01  fof(f51,plain,(
% 2.23/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/1.01    inference(cnf_transformation,[],[f20])).
% 2.23/1.01  
% 2.23/1.01  fof(f6,axiom,(
% 2.23/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f23,plain,(
% 2.23/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.23/1.01    inference(ennf_transformation,[],[f6])).
% 2.23/1.01  
% 2.23/1.01  fof(f24,plain,(
% 2.23/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.23/1.01    inference(flattening,[],[f23])).
% 2.23/1.01  
% 2.23/1.01  fof(f40,plain,(
% 2.23/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.23/1.01    inference(nnf_transformation,[],[f24])).
% 2.23/1.01  
% 2.23/1.01  fof(f54,plain,(
% 2.23/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f40])).
% 2.23/1.01  
% 2.23/1.01  fof(f3,axiom,(
% 2.23/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f19,plain,(
% 2.23/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/1.01    inference(ennf_transformation,[],[f3])).
% 2.23/1.01  
% 2.23/1.01  fof(f50,plain,(
% 2.23/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/1.01    inference(cnf_transformation,[],[f19])).
% 2.23/1.01  
% 2.23/1.01  fof(f8,axiom,(
% 2.23/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f27,plain,(
% 2.23/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.23/1.01    inference(ennf_transformation,[],[f8])).
% 2.23/1.01  
% 2.23/1.01  fof(f57,plain,(
% 2.23/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f27])).
% 2.23/1.01  
% 2.23/1.01  fof(f10,axiom,(
% 2.23/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f29,plain,(
% 2.23/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.23/1.01    inference(ennf_transformation,[],[f10])).
% 2.23/1.01  
% 2.23/1.01  fof(f30,plain,(
% 2.23/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.23/1.01    inference(flattening,[],[f29])).
% 2.23/1.01  
% 2.23/1.01  fof(f59,plain,(
% 2.23/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f30])).
% 2.23/1.01  
% 2.23/1.01  fof(f66,plain,(
% 2.23/1.01    l1_pre_topc(sK0)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f64,plain,(
% 2.23/1.01    ~v2_struct_0(sK0)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f72,plain,(
% 2.23/1.01    v1_funct_1(sK3)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f73,plain,(
% 2.23/1.01    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f75,plain,(
% 2.23/1.01    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f11,axiom,(
% 2.23/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f31,plain,(
% 2.23/1.01    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.23/1.01    inference(ennf_transformation,[],[f11])).
% 2.23/1.01  
% 2.23/1.01  fof(f60,plain,(
% 2.23/1.01    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.23/1.01    inference(cnf_transformation,[],[f31])).
% 2.23/1.01  
% 2.23/1.01  fof(f9,axiom,(
% 2.23/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f28,plain,(
% 2.23/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.23/1.01    inference(ennf_transformation,[],[f9])).
% 2.23/1.01  
% 2.23/1.01  fof(f58,plain,(
% 2.23/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f28])).
% 2.23/1.01  
% 2.23/1.01  fof(f69,plain,(
% 2.23/1.01    l1_pre_topc(sK1)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f13,axiom,(
% 2.23/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f34,plain,(
% 2.23/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/1.01    inference(ennf_transformation,[],[f13])).
% 2.23/1.01  
% 2.23/1.01  fof(f35,plain,(
% 2.23/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/1.01    inference(flattening,[],[f34])).
% 2.23/1.01  
% 2.23/1.01  fof(f63,plain,(
% 2.23/1.01    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f35])).
% 2.23/1.01  
% 2.23/1.01  fof(f71,plain,(
% 2.23/1.01    m1_pre_topc(sK2,sK1)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f67,plain,(
% 2.23/1.01    ~v2_struct_0(sK1)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f68,plain,(
% 2.23/1.01    v2_pre_topc(sK1)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f65,plain,(
% 2.23/1.01    v2_pre_topc(sK0)),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  fof(f1,axiom,(
% 2.23/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f38,plain,(
% 2.23/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/1.01    inference(nnf_transformation,[],[f1])).
% 2.23/1.01  
% 2.23/1.01  fof(f39,plain,(
% 2.23/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/1.01    inference(flattening,[],[f38])).
% 2.23/1.01  
% 2.23/1.01  fof(f46,plain,(
% 2.23/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.23/1.01    inference(cnf_transformation,[],[f39])).
% 2.23/1.01  
% 2.23/1.01  fof(f78,plain,(
% 2.23/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.23/1.01    inference(equality_resolution,[],[f46])).
% 2.23/1.01  
% 2.23/1.01  fof(f2,axiom,(
% 2.23/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f17,plain,(
% 2.23/1.01    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/1.01    inference(ennf_transformation,[],[f2])).
% 2.23/1.01  
% 2.23/1.01  fof(f18,plain,(
% 2.23/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.23/1.01    inference(flattening,[],[f17])).
% 2.23/1.01  
% 2.23/1.01  fof(f49,plain,(
% 2.23/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f18])).
% 2.23/1.01  
% 2.23/1.01  fof(f7,axiom,(
% 2.23/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f25,plain,(
% 2.23/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.23/1.01    inference(ennf_transformation,[],[f7])).
% 2.23/1.01  
% 2.23/1.01  fof(f26,plain,(
% 2.23/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.23/1.01    inference(flattening,[],[f25])).
% 2.23/1.01  
% 2.23/1.01  fof(f56,plain,(
% 2.23/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f26])).
% 2.23/1.01  
% 2.23/1.01  fof(f12,axiom,(
% 2.23/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 2.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/1.01  
% 2.23/1.01  fof(f32,plain,(
% 2.23/1.01    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.23/1.01    inference(ennf_transformation,[],[f12])).
% 2.23/1.01  
% 2.23/1.01  fof(f33,plain,(
% 2.23/1.01    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.23/1.01    inference(flattening,[],[f32])).
% 2.23/1.01  
% 2.23/1.01  fof(f62,plain,(
% 2.23/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.23/1.01    inference(cnf_transformation,[],[f33])).
% 2.23/1.01  
% 2.23/1.01  fof(f76,plain,(
% 2.23/1.01    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.23/1.01    inference(cnf_transformation,[],[f45])).
% 2.23/1.01  
% 2.23/1.01  cnf(c_20,negated_conjecture,
% 2.23/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 2.23/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1138,plain,
% 2.23/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_6,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.23/1.01      | v1_partfun1(X0,X1)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | v1_xboole_0(X2)
% 2.23/1.01      | ~ v1_funct_1(X0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_5,plain,
% 2.23/1.01      ( v4_relat_1(X0,X1)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.23/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_9,plain,
% 2.23/1.01      ( ~ v1_partfun1(X0,X1)
% 2.23/1.01      | ~ v4_relat_1(X0,X1)
% 2.23/1.01      | ~ v1_relat_1(X0)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_336,plain,
% 2.23/1.01      ( ~ v1_partfun1(X0,X1)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ v1_relat_1(X0)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_4,plain,
% 2.23/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | v1_relat_1(X0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_340,plain,
% 2.23/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ v1_partfun1(X0,X1)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_336,c_9,c_5,c_4]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_341,plain,
% 2.23/1.01      ( ~ v1_partfun1(X0,X1)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(renaming,[status(thm)],[c_340]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_436,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.23/1.01      | v1_xboole_0(X2)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(resolution,[status(thm)],[c_6,c_341]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_440,plain,
% 2.23/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ v1_funct_2(X0,X1,X2)
% 2.23/1.01      | v1_xboole_0(X2)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_436,c_9,c_6,c_5,c_4]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_441,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | v1_xboole_0(X2)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(renaming,[status(thm)],[c_440]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_11,plain,
% 2.23/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_13,plain,
% 2.23/1.01      ( v2_struct_0(X0)
% 2.23/1.01      | ~ l1_struct_0(X0)
% 2.23/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.23/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_318,plain,
% 2.23/1.01      ( v2_struct_0(X0)
% 2.23/1.01      | ~ l1_pre_topc(X0)
% 2.23/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.23/1.01      inference(resolution,[status(thm)],[c_11,c_13]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_28,negated_conjecture,
% 2.23/1.01      ( l1_pre_topc(sK0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_583,plain,
% 2.23/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 2.23/1.01      inference(resolution_lifted,[status(thm)],[c_318,c_28]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_584,plain,
% 2.23/1.01      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 2.23/1.01      inference(unflattening,[status(thm)],[c_583]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_30,negated_conjecture,
% 2.23/1.01      ( ~ v2_struct_0(sK0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_586,plain,
% 2.23/1.01      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_584,c_30]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_631,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | u1_struct_0(sK0) != X2
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(resolution_lifted,[status(thm)],[c_441,c_586]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_632,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0))))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k1_relat_1(X0) = X1 ),
% 2.23/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1128,plain,
% 2.23/1.01      ( k1_relat_1(X0) = X1
% 2.23/1.01      | v1_funct_2(X0,X1,u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1528,plain,
% 2.23/1.01      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 2.23/1.01      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1138,c_1128]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_22,negated_conjecture,
% 2.23/1.01      ( v1_funct_1(sK3) ),
% 2.23/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_39,plain,
% 2.23/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_21,negated_conjecture,
% 2.23/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 2.23/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_40,plain,
% 2.23/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1876,plain,
% 2.23/1.01      ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_1528,c_39,c_40]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_19,negated_conjecture,
% 2.23/1.01      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.23/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1884,plain,
% 2.23/1.01      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_1876,c_19]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_15,plain,
% 2.23/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.23/1.01      | X2 = X1
% 2.23/1.01      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1139,plain,
% 2.23/1.01      ( X0 = X1
% 2.23/1.01      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.23/1.01      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2337,plain,
% 2.23/1.01      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.23/1.01      | u1_struct_0(sK2) = X0
% 2.23/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1884,c_1139]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2515,plain,
% 2.23/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 2.23/1.01      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK3)))) != iProver_top ),
% 2.23/1.01      inference(equality_resolution,[status(thm)],[c_2337]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_12,plain,
% 2.23/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.23/1.01      | ~ l1_pre_topc(X0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_25,negated_conjecture,
% 2.23/1.01      ( l1_pre_topc(sK1) ),
% 2.23/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_576,plain,
% 2.23/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.23/1.01      | sK1 != X0 ),
% 2.23/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_577,plain,
% 2.23/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 2.23/1.01      inference(unflattening,[status(thm)],[c_576]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1133,plain,
% 2.23/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1881,plain,
% 2.23/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK3)))) = iProver_top ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_1876,c_1133]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2741,plain,
% 2.23/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_2515,c_1881]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_17,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.23/1.01      | ~ m1_pre_topc(X3,X1)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/1.01      | ~ v2_pre_topc(X2)
% 2.23/1.01      | ~ v2_pre_topc(X1)
% 2.23/1.01      | v2_struct_0(X1)
% 2.23/1.01      | v2_struct_0(X2)
% 2.23/1.01      | ~ l1_pre_topc(X1)
% 2.23/1.01      | ~ l1_pre_topc(X2)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.23/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_23,negated_conjecture,
% 2.23/1.01      ( m1_pre_topc(sK2,sK1) ),
% 2.23/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_468,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/1.01      | ~ v2_pre_topc(X1)
% 2.23/1.01      | ~ v2_pre_topc(X2)
% 2.23/1.01      | v2_struct_0(X1)
% 2.23/1.01      | v2_struct_0(X2)
% 2.23/1.01      | ~ l1_pre_topc(X1)
% 2.23/1.01      | ~ l1_pre_topc(X2)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.23/1.01      | sK2 != X3
% 2.23/1.01      | sK1 != X1 ),
% 2.23/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_469,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.23/1.01      | ~ v2_pre_topc(X1)
% 2.23/1.01      | ~ v2_pre_topc(sK1)
% 2.23/1.01      | v2_struct_0(X1)
% 2.23/1.01      | v2_struct_0(sK1)
% 2.23/1.01      | ~ l1_pre_topc(X1)
% 2.23/1.01      | ~ l1_pre_topc(sK1)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 2.23/1.01      inference(unflattening,[status(thm)],[c_468]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_27,negated_conjecture,
% 2.23/1.01      ( ~ v2_struct_0(sK1) ),
% 2.23/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_26,negated_conjecture,
% 2.23/1.01      ( v2_pre_topc(sK1) ),
% 2.23/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_473,plain,
% 2.23/1.01      ( ~ l1_pre_topc(X1)
% 2.23/1.01      | ~ v2_pre_topc(X1)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.23/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.23/1.01      | v2_struct_0(X1)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_469,c_27,c_26,c_25]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_474,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.23/1.01      | ~ v2_pre_topc(X1)
% 2.23/1.01      | v2_struct_0(X1)
% 2.23/1.01      | ~ l1_pre_topc(X1)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 2.23/1.01      inference(renaming,[status(thm)],[c_473]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_29,negated_conjecture,
% 2.23/1.01      ( v2_pre_topc(sK0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_531,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.23/1.01      | v2_struct_0(X1)
% 2.23/1.01      | ~ l1_pre_topc(X1)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
% 2.23/1.01      | sK0 != X1 ),
% 2.23/1.01      inference(resolution_lifted,[status(thm)],[c_474,c_29]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_532,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.23/1.01      | v2_struct_0(sK0)
% 2.23/1.01      | ~ l1_pre_topc(sK0)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
% 2.23/1.01      inference(unflattening,[status(thm)],[c_531]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_536,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_532,c_30,c_28]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1134,plain,
% 2.23/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2)
% 2.23/1.01      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1385,plain,
% 2.23/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
% 2.23/1.01      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1138,c_1134]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1287,plain,
% 2.23/1.01      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.23/1.01      | ~ v1_funct_1(sK3)
% 2.23/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(instantiation,[status(thm)],[c_536]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1388,plain,
% 2.23/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_1385,c_22,c_21,c_20,c_1287]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1879,plain,
% 2.23/1.01      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_1876,c_1388]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2747,plain,
% 2.23/1.01      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_2741,c_1879]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1142,plain,
% 2.23/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.23/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1628,plain,
% 2.23/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1138,c_1142]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2,plain,
% 2.23/1.01      ( r1_tarski(X0,X0) ),
% 2.23/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1144,plain,
% 2.23/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_3,plain,
% 2.23/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.23/1.01      | ~ v1_relat_1(X0)
% 2.23/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.23/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1143,plain,
% 2.23/1.01      ( k7_relat_1(X0,X1) = X0
% 2.23/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.23/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1715,plain,
% 2.23/1.01      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.23/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1144,c_1143]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2940,plain,
% 2.23/1.01      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1628,c_1715]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1882,plain,
% 2.23/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_1876,c_1138]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_10,plain,
% 2.23/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.23/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1141,plain,
% 2.23/1.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 2.23/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.23/1.01      | v1_funct_1(X2) != iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2506,plain,
% 2.23/1.01      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
% 2.23/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1882,c_1141]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_3026,plain,
% 2.23/1.01      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.23/1.01      inference(global_propositional_subsumption,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_2506,c_39]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_3343,plain,
% 2.23/1.01      ( k2_tmap_1(sK1,sK0,sK3,sK2) = sK3 ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_2747,c_2940,c_3026]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_16,plain,
% 2.23/1.01      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.23/1.01      | ~ v1_funct_2(X5,X2,X3)
% 2.23/1.01      | ~ v1_funct_2(X4,X0,X1)
% 2.23/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.23/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.23/1.01      | v1_xboole_0(X1)
% 2.23/1.01      | v1_xboole_0(X3)
% 2.23/1.01      | ~ v1_funct_1(X5)
% 2.23/1.01      | ~ v1_funct_1(X4) ),
% 2.23/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_18,negated_conjecture,
% 2.23/1.01      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 2.23/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_397,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.23/1.01      | ~ v1_funct_2(X3,X4,X5)
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.23/1.01      | v1_xboole_0(X5)
% 2.23/1.01      | v1_xboole_0(X2)
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | ~ v1_funct_1(X3)
% 2.23/1.01      | k2_tmap_1(sK1,sK0,sK3,sK2) != X3
% 2.23/1.01      | u1_struct_0(sK2) != X1
% 2.23/1.01      | u1_struct_0(sK0) != X2
% 2.23/1.01      | u1_struct_0(sK0) != X5
% 2.23/1.01      | u1_struct_0(sK1) != X4
% 2.23/1.01      | sK3 != X3 ),
% 2.23/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_398,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
% 2.23/1.01      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.23/1.01      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.23/1.01      | v1_xboole_0(u1_struct_0(sK0))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.23/1.01      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(unflattening,[status(thm)],[c_397]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_606,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
% 2.23/1.01      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.23/1.01      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.23/1.01      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(backward_subsumption_resolution,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_586,c_398]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_792,plain,
% 2.23/1.01      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.23/1.01      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.23/1.01      | sP0_iProver_split
% 2.23/1.01      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.23/1.01      inference(splitting,
% 2.23/1.01                [splitting(split),new_symbols(definition,[])],
% 2.23/1.01                [c_606]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1130,plain,
% 2.23/1.01      ( sK3 != k2_tmap_1(sK1,sK0,sK3,sK2)
% 2.23/1.01      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top
% 2.23/1.01      | sP0_iProver_split = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_2930,plain,
% 2.23/1.01      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.23/1.01      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top
% 2.23/1.01      | sP0_iProver_split = iProver_top ),
% 2.23/1.01      inference(light_normalisation,[status(thm)],[c_1130,c_1876]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_3345,plain,
% 2.23/1.01      ( sK3 != sK3
% 2.23/1.01      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(sK3) != iProver_top
% 2.23/1.01      | sP0_iProver_split = iProver_top ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_3343,c_2930]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_791,plain,
% 2.23/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
% 2.23/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.23/1.01      | ~ v1_funct_1(X0)
% 2.23/1.01      | ~ sP0_iProver_split ),
% 2.23/1.01      inference(splitting,
% 2.23/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.23/1.01                [c_606]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1131,plain,
% 2.23/1.01      ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(X0) != iProver_top
% 2.23/1.01      | sP0_iProver_split != iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_3214,plain,
% 2.23/1.01      ( v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/1.01      | v1_funct_1(X0) != iProver_top
% 2.23/1.01      | sP0_iProver_split != iProver_top ),
% 2.23/1.01      inference(light_normalisation,[status(thm)],[c_1131,c_2741]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_3222,plain,
% 2.23/1.01      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.23/1.01      | v1_funct_1(sK3) != iProver_top
% 2.23/1.01      | sP0_iProver_split != iProver_top ),
% 2.23/1.01      inference(superposition,[status(thm)],[c_1882,c_3214]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1137,plain,
% 2.23/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.23/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1883,plain,
% 2.23/1.01      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 2.23/1.01      inference(demodulation,[status(thm)],[c_1876,c_1137]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_794,plain,( X0 = X0 ),theory(equality) ).
% 2.23/1.01  
% 2.23/1.01  cnf(c_1375,plain,
% 2.23/1.01      ( sK3 = sK3 ),
% 2.23/1.01      inference(instantiation,[status(thm)],[c_794]) ).
% 2.23/1.01  
% 2.23/1.01  cnf(contradiction,plain,
% 2.23/1.01      ( $false ),
% 2.23/1.01      inference(minisat,
% 2.23/1.01                [status(thm)],
% 2.23/1.01                [c_3345,c_3222,c_1883,c_1882,c_1375,c_39]) ).
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.23/1.01  
% 2.23/1.01  ------                               Statistics
% 2.23/1.01  
% 2.23/1.01  ------ General
% 2.23/1.01  
% 2.23/1.01  abstr_ref_over_cycles:                  0
% 2.23/1.01  abstr_ref_under_cycles:                 0
% 2.23/1.01  gc_basic_clause_elim:                   0
% 2.23/1.01  forced_gc_time:                         0
% 2.23/1.01  parsing_time:                           0.016
% 2.23/1.01  unif_index_cands_time:                  0.
% 2.23/1.01  unif_index_add_time:                    0.
% 2.23/1.01  orderings_time:                         0.
% 2.23/1.01  out_proof_time:                         0.013
% 2.23/1.01  total_time:                             0.242
% 2.23/1.01  num_of_symbols:                         59
% 2.23/1.01  num_of_terms:                           3784
% 2.23/1.01  
% 2.23/1.01  ------ Preprocessing
% 2.23/1.01  
% 2.23/1.01  num_of_splits:                          1
% 2.23/1.01  num_of_split_atoms:                     1
% 2.23/1.01  num_of_reused_defs:                     0
% 2.23/1.01  num_eq_ax_congr_red:                    21
% 2.23/1.01  num_of_sem_filtered_clauses:            1
% 2.23/1.01  num_of_subtypes:                        0
% 2.23/1.01  monotx_restored_types:                  0
% 2.23/1.01  sat_num_of_epr_types:                   0
% 2.23/1.01  sat_num_of_non_cyclic_types:            0
% 2.23/1.01  sat_guarded_non_collapsed_types:        0
% 2.23/1.01  num_pure_diseq_elim:                    0
% 2.23/1.01  simp_replaced_by:                       0
% 2.23/1.01  res_preprocessed:                       112
% 2.23/1.01  prep_upred:                             0
% 2.23/1.01  prep_unflattend:                        19
% 2.23/1.01  smt_new_axioms:                         0
% 2.23/1.01  pred_elim_cands:                        5
% 2.23/1.01  pred_elim:                              9
% 2.23/1.01  pred_elim_cl:                           11
% 2.23/1.01  pred_elim_cycles:                       12
% 2.23/1.01  merged_defs:                            0
% 2.23/1.01  merged_defs_ncl:                        0
% 2.23/1.01  bin_hyper_res:                          0
% 2.23/1.01  prep_cycles:                            4
% 2.23/1.01  pred_elim_time:                         0.013
% 2.23/1.01  splitting_time:                         0.
% 2.23/1.01  sem_filter_time:                        0.
% 2.23/1.01  monotx_time:                            0.001
% 2.23/1.01  subtype_inf_time:                       0.
% 2.23/1.01  
% 2.23/1.01  ------ Problem properties
% 2.23/1.01  
% 2.23/1.01  clauses:                                19
% 2.23/1.01  conjectures:                            4
% 2.23/1.01  epr:                                    3
% 2.23/1.01  horn:                                   19
% 2.23/1.01  ground:                                 7
% 2.23/1.01  unary:                                  7
% 2.23/1.01  binary:                                 1
% 2.23/1.01  lits:                                   49
% 2.23/1.01  lits_eq:                                13
% 2.23/1.01  fd_pure:                                0
% 2.23/1.01  fd_pseudo:                              0
% 2.23/1.01  fd_cond:                                0
% 2.23/1.01  fd_pseudo_cond:                         5
% 2.23/1.01  ac_symbols:                             0
% 2.23/1.01  
% 2.23/1.01  ------ Propositional Solver
% 2.23/1.01  
% 2.23/1.01  prop_solver_calls:                      27
% 2.23/1.01  prop_fast_solver_calls:                 817
% 2.23/1.01  smt_solver_calls:                       0
% 2.23/1.01  smt_fast_solver_calls:                  0
% 2.23/1.01  prop_num_of_clauses:                    1214
% 2.23/1.01  prop_preprocess_simplified:             4450
% 2.23/1.01  prop_fo_subsumed:                       20
% 2.23/1.01  prop_solver_time:                       0.
% 2.23/1.01  smt_solver_time:                        0.
% 2.23/1.01  smt_fast_solver_time:                   0.
% 2.23/1.01  prop_fast_solver_time:                  0.
% 2.23/1.01  prop_unsat_core_time:                   0.
% 2.23/1.01  
% 2.23/1.01  ------ QBF
% 2.23/1.01  
% 2.23/1.01  qbf_q_res:                              0
% 2.23/1.01  qbf_num_tautologies:                    0
% 2.23/1.01  qbf_prep_cycles:                        0
% 2.23/1.01  
% 2.23/1.01  ------ BMC1
% 2.23/1.01  
% 2.23/1.01  bmc1_current_bound:                     -1
% 2.23/1.01  bmc1_last_solved_bound:                 -1
% 2.23/1.01  bmc1_unsat_core_size:                   -1
% 2.23/1.01  bmc1_unsat_core_parents_size:           -1
% 2.23/1.01  bmc1_merge_next_fun:                    0
% 2.23/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.23/1.01  
% 2.23/1.01  ------ Instantiation
% 2.23/1.01  
% 2.23/1.01  inst_num_of_clauses:                    366
% 2.23/1.01  inst_num_in_passive:                    70
% 2.23/1.01  inst_num_in_active:                     208
% 2.23/1.01  inst_num_in_unprocessed:                90
% 2.23/1.01  inst_num_of_loops:                      210
% 2.23/1.01  inst_num_of_learning_restarts:          0
% 2.23/1.01  inst_num_moves_active_passive:          0
% 2.23/1.01  inst_lit_activity:                      0
% 2.23/1.01  inst_lit_activity_moves:                0
% 2.23/1.01  inst_num_tautologies:                   0
% 2.23/1.01  inst_num_prop_implied:                  0
% 2.23/1.01  inst_num_existing_simplified:           0
% 2.23/1.01  inst_num_eq_res_simplified:             0
% 2.23/1.01  inst_num_child_elim:                    0
% 2.23/1.01  inst_num_of_dismatching_blockings:      100
% 2.23/1.01  inst_num_of_non_proper_insts:           494
% 2.23/1.01  inst_num_of_duplicates:                 0
% 2.23/1.01  inst_inst_num_from_inst_to_res:         0
% 2.23/1.01  inst_dismatching_checking_time:         0.
% 2.23/1.01  
% 2.23/1.01  ------ Resolution
% 2.23/1.01  
% 2.23/1.01  res_num_of_clauses:                     0
% 2.23/1.01  res_num_in_passive:                     0
% 2.23/1.01  res_num_in_active:                      0
% 2.23/1.01  res_num_of_loops:                       116
% 2.23/1.01  res_forward_subset_subsumed:            57
% 2.23/1.01  res_backward_subset_subsumed:           4
% 2.23/1.01  res_forward_subsumed:                   0
% 2.23/1.01  res_backward_subsumed:                  0
% 2.23/1.01  res_forward_subsumption_resolution:     1
% 2.23/1.01  res_backward_subsumption_resolution:    1
% 2.23/1.01  res_clause_to_clause_subsumption:       87
% 2.23/1.01  res_orphan_elimination:                 0
% 2.23/1.01  res_tautology_del:                      34
% 2.23/1.01  res_num_eq_res_simplified:              0
% 2.23/1.01  res_num_sel_changes:                    0
% 2.23/1.01  res_moves_from_active_to_pass:          0
% 2.23/1.01  
% 2.23/1.01  ------ Superposition
% 2.23/1.01  
% 2.23/1.01  sup_time_total:                         0.
% 2.23/1.01  sup_time_generating:                    0.
% 2.23/1.01  sup_time_sim_full:                      0.
% 2.23/1.01  sup_time_sim_immed:                     0.
% 2.23/1.01  
% 2.23/1.01  sup_num_of_clauses:                     32
% 2.23/1.01  sup_num_in_active:                      26
% 2.23/1.01  sup_num_in_passive:                     6
% 2.23/1.01  sup_num_of_loops:                       41
% 2.23/1.01  sup_fw_superposition:                   17
% 2.23/1.01  sup_bw_superposition:                   7
% 2.23/1.01  sup_immediate_simplified:               3
% 2.23/1.01  sup_given_eliminated:                   0
% 2.23/1.01  comparisons_done:                       0
% 2.23/1.01  comparisons_avoided:                    0
% 2.23/1.01  
% 2.23/1.01  ------ Simplifications
% 2.23/1.01  
% 2.23/1.01  
% 2.23/1.01  sim_fw_subset_subsumed:                 1
% 2.23/1.01  sim_bw_subset_subsumed:                 2
% 2.23/1.01  sim_fw_subsumed:                        2
% 2.23/1.01  sim_bw_subsumed:                        0
% 2.23/1.01  sim_fw_subsumption_res:                 2
% 2.23/1.01  sim_bw_subsumption_res:                 0
% 2.23/1.01  sim_tautology_del:                      0
% 2.23/1.01  sim_eq_tautology_del:                   10
% 2.23/1.01  sim_eq_res_simp:                        0
% 2.23/1.01  sim_fw_demodulated:                     2
% 2.23/1.01  sim_bw_demodulated:                     15
% 2.23/1.01  sim_light_normalised:                   7
% 2.23/1.01  sim_joinable_taut:                      0
% 2.23/1.01  sim_joinable_simp:                      0
% 2.23/1.01  sim_ac_normalised:                      0
% 2.23/1.01  sim_smt_subsumption:                    0
% 2.23/1.01  
%------------------------------------------------------------------------------
