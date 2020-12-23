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
% DateTime   : Thu Dec  3 12:22:25 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  233 (1977 expanded)
%              Number of clauses        :  143 ( 552 expanded)
%              Number of leaves         :   27 ( 641 expanded)
%              Depth                    :   22
%              Number of atoms          :  813 (16840 expanded)
%              Number of equality atoms :  278 (2052 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f58,f57,f56,f55])).

fof(f93,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f45])).

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
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
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

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1090,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_265,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_12])).

cnf(c_266,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_1077,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1095,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3033,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1095])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1571,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_12,c_27])).

cnf(c_1572,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_3060,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_40,c_1572])).

cnf(c_3061,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3060])).

cnf(c_3068,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_3061])).

cnf(c_3302,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3068,c_40])).

cnf(c_3303,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3302])).

cnf(c_3310,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3303])).

cnf(c_47,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_49,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_62,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_64,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_3057,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_3574,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3310,c_40,c_49,c_64,c_1572,c_3057])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1088,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1102,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4037,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1102])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1461,plain,
    ( l1_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_11,c_32])).

cnf(c_1462,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_1473,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1593,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_1594,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1593])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1817,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1818,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_4523,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4037,c_35,c_43,c_44,c_45,c_1462,c_1594,c_1818])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1100,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4528,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v4_relat_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4523,c_1100])).

cnf(c_478,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_498,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_463,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_506,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1421,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1535,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1709,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_464,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1933,plain,
    ( X0 != X1
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_2395,plain,
    ( X0 != u1_struct_0(sK1)
    | u1_struct_0(sK1) = X0
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_3370,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_4960,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4528,c_34,c_26,c_25,c_24,c_498,c_506,c_1397,c_1421,c_1461,c_1593,c_1709,c_1817,c_3370])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1091,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1108,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2027,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1108])).

cnf(c_5025,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4960,c_2027])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3883,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1103])).

cnf(c_1104,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4311,plain,
    ( v4_relat_1(sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_1104])).

cnf(c_8479,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | v4_relat_1(sK3,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5025,c_4311])).

cnf(c_1,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1107,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9822,plain,
    ( k7_relat_1(sK3,u1_struct_0(X0)) = sK3
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8479,c_1107])).

cnf(c_1398,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1397])).

cnf(c_10554,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(X0)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9822,c_45,c_1398])).

cnf(c_10555,plain,
    ( k7_relat_1(sK3,u1_struct_0(X0)) = sK3
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10554])).

cnf(c_10564,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3574,c_10555])).

cnf(c_11514,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10564,c_40,c_1572])).

cnf(c_1085,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5032,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4960,c_1091])).

cnf(c_7182,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5032,c_40])).

cnf(c_7183,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7182])).

cnf(c_7191,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7183,c_1108])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1106,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7516,plain,
    ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7191,c_1106])).

cnf(c_7532,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k1_relat_1(k7_relat_1(sK3,u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7516,c_45,c_1398])).

cnf(c_7533,plain,
    ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7532])).

cnf(c_7541,plain,
    ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1085,c_7533])).

cnf(c_11519,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11514,c_7541])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1099,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3875,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1099])).

cnf(c_1478,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_4289,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_26,c_24,c_1596])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_1092,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2883,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1092])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3453,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2883,c_35,c_36,c_37,c_38,c_39,c_40,c_43,c_44])).

cnf(c_3454,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3453])).

cnf(c_3462,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1085,c_3454])).

cnf(c_4294,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_4289,c_3462])).

cnf(c_22,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1089,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4531,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4294,c_1089])).

cnf(c_4963,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4960,c_4531])).

cnf(c_11520,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11514,c_4963])).

cnf(c_11527,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11519,c_11520])).

cnf(c_17,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1520,plain,
    ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,X2,X3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4512,plain,
    ( r1_funct_2(X0,X1,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_8420,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4512])).

cnf(c_8430,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) = iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8420])).

cnf(c_4973,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4960,c_1088])).

cnf(c_472,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_1483,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | X2 != u1_struct_0(sK0)
    | X1 != u1_struct_0(sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_1670,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | X1 != u1_struct_0(sK0)
    | X0 != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_2149,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),X0)
    | X0 != u1_struct_0(sK0)
    | k1_relat_1(sK3) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_3181,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_relat_1(sK3) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_3184,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_relat_1(sK3) != u1_struct_0(sK1)
    | sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3181])).

cnf(c_1784,plain,
    ( u1_struct_0(X0) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_2327,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_1587,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11527,c_8430,c_4973,c_3184,c_2327,c_1818,c_1817,c_1709,c_1593,c_1587,c_1462,c_1461,c_1421,c_1397,c_24,c_44,c_25,c_43,c_26,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.80/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/0.99  
% 3.80/0.99  ------  iProver source info
% 3.80/0.99  
% 3.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/0.99  git: non_committed_changes: false
% 3.80/0.99  git: last_make_outside_of_git: false
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  ------ Parsing...
% 3.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/0.99  ------ Proving...
% 3.80/0.99  ------ Problem Properties 
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  clauses                                 33
% 3.80/0.99  conjectures                             13
% 3.80/0.99  EPR                                     12
% 3.80/0.99  Horn                                    29
% 3.80/0.99  unary                                   13
% 3.80/0.99  binary                                  5
% 3.80/0.99  lits                                    91
% 3.80/0.99  lits eq                                 7
% 3.80/0.99  fd_pure                                 0
% 3.80/0.99  fd_pseudo                               0
% 3.80/0.99  fd_cond                                 0
% 3.80/0.99  fd_pseudo_cond                          2
% 3.80/0.99  AC symbols                              0
% 3.80/0.99  
% 3.80/0.99  ------ Input Options Time Limit: Unbounded
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  Current options:
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ Proving...
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS status Theorem for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  fof(f18,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f49,plain,(
% 3.80/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f18])).
% 3.80/0.99  
% 3.80/0.99  fof(f81,plain,(
% 3.80/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f49])).
% 3.80/0.99  
% 3.80/0.99  fof(f14,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f43,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f14])).
% 3.80/0.99  
% 3.80/0.99  fof(f53,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(nnf_transformation,[],[f43])).
% 3.80/0.99  
% 3.80/0.99  fof(f75,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f53])).
% 3.80/0.99  
% 3.80/0.99  fof(f11,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f39,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f11])).
% 3.80/0.99  
% 3.80/0.99  fof(f72,plain,(
% 3.80/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f39])).
% 3.80/0.99  
% 3.80/0.99  fof(f19,conjecture,(
% 3.80/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f20,negated_conjecture,(
% 3.80/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.80/0.99    inference(negated_conjecture,[],[f19])).
% 3.80/0.99  
% 3.80/0.99  fof(f50,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.80/0.99    inference(ennf_transformation,[],[f20])).
% 3.80/0.99  
% 3.80/0.99  fof(f51,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.80/0.99    inference(flattening,[],[f50])).
% 3.80/0.99  
% 3.80/0.99  fof(f58,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f57,plain,(
% 3.80/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f56,plain,(
% 3.80/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f55,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f59,plain,(
% 3.80/0.99    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f58,f57,f56,f55])).
% 3.80/0.99  
% 3.80/0.99  fof(f93,plain,(
% 3.80/0.99    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f13,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f42,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f13])).
% 3.80/0.99  
% 3.80/0.99  fof(f74,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f42])).
% 3.80/0.99  
% 3.80/0.99  fof(f87,plain,(
% 3.80/0.99    l1_pre_topc(sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f89,plain,(
% 3.80/0.99    m1_pre_topc(sK2,sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f92,plain,(
% 3.80/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f7,axiom,(
% 3.80/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f32,plain,(
% 3.80/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.80/0.99    inference(ennf_transformation,[],[f7])).
% 3.80/0.99  
% 3.80/0.99  fof(f33,plain,(
% 3.80/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.80/0.99    inference(flattening,[],[f32])).
% 3.80/0.99  
% 3.80/0.99  fof(f67,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f82,plain,(
% 3.80/0.99    ~v2_struct_0(sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f90,plain,(
% 3.80/0.99    v1_funct_1(sK3)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f91,plain,(
% 3.80/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f10,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f38,plain,(
% 3.80/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f10])).
% 3.80/0.99  
% 3.80/0.99  fof(f71,plain,(
% 3.80/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f84,plain,(
% 3.80/0.99    l1_pre_topc(sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f12,axiom,(
% 3.80/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f40,plain,(
% 3.80/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.80/0.99    inference(ennf_transformation,[],[f12])).
% 3.80/0.99  
% 3.80/0.99  fof(f41,plain,(
% 3.80/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.80/0.99    inference(flattening,[],[f40])).
% 3.80/0.99  
% 3.80/0.99  fof(f73,plain,(
% 3.80/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f41])).
% 3.80/0.99  
% 3.80/0.99  fof(f8,axiom,(
% 3.80/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f34,plain,(
% 3.80/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f8])).
% 3.80/0.99  
% 3.80/0.99  fof(f35,plain,(
% 3.80/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(flattening,[],[f34])).
% 3.80/0.99  
% 3.80/0.99  fof(f52,plain,(
% 3.80/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f35])).
% 3.80/0.99  
% 3.80/0.99  fof(f68,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f52])).
% 3.80/0.99  
% 3.80/0.99  fof(f4,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f28,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(ennf_transformation,[],[f4])).
% 3.80/0.99  
% 3.80/0.99  fof(f63,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f28])).
% 3.80/0.99  
% 3.80/0.99  fof(f5,axiom,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f22,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.80/0.99    inference(pure_predicate_removal,[],[f5])).
% 3.80/0.99  
% 3.80/0.99  fof(f29,plain,(
% 3.80/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.99    inference(ennf_transformation,[],[f22])).
% 3.80/0.99  
% 3.80/0.99  fof(f64,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f29])).
% 3.80/0.99  
% 3.80/0.99  fof(f17,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f48,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f17])).
% 3.80/0.99  
% 3.80/0.99  fof(f80,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f48])).
% 3.80/0.99  
% 3.80/0.99  fof(f1,axiom,(
% 3.80/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f21,plain,(
% 3.80/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.80/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.80/0.99  
% 3.80/0.99  fof(f23,plain,(
% 3.80/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f21])).
% 3.80/0.99  
% 3.80/0.99  fof(f60,plain,(
% 3.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f23])).
% 3.80/0.99  
% 3.80/0.99  fof(f6,axiom,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f30,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.80/0.99    inference(ennf_transformation,[],[f6])).
% 3.80/0.99  
% 3.80/0.99  fof(f31,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.80/0.99    inference(flattening,[],[f30])).
% 3.80/0.99  
% 3.80/0.99  fof(f65,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f31])).
% 3.80/0.99  
% 3.80/0.99  fof(f2,axiom,(
% 3.80/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f24,plain,(
% 3.80/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f2])).
% 3.80/0.99  
% 3.80/0.99  fof(f25,plain,(
% 3.80/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(flattening,[],[f24])).
% 3.80/0.99  
% 3.80/0.99  fof(f61,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f25])).
% 3.80/0.99  
% 3.80/0.99  fof(f3,axiom,(
% 3.80/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f26,plain,(
% 3.80/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(ennf_transformation,[],[f3])).
% 3.80/0.99  
% 3.80/0.99  fof(f27,plain,(
% 3.80/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.80/0.99    inference(flattening,[],[f26])).
% 3.80/0.99  
% 3.80/0.99  fof(f62,plain,(
% 3.80/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f27])).
% 3.80/0.99  
% 3.80/0.99  fof(f9,axiom,(
% 3.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f36,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.80/0.99    inference(ennf_transformation,[],[f9])).
% 3.80/0.99  
% 3.80/0.99  fof(f37,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.80/0.99    inference(flattening,[],[f36])).
% 3.80/0.99  
% 3.80/0.99  fof(f70,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f37])).
% 3.80/0.99  
% 3.80/0.99  fof(f16,axiom,(
% 3.80/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f46,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.99    inference(ennf_transformation,[],[f16])).
% 3.80/0.99  
% 3.80/0.99  fof(f47,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.99    inference(flattening,[],[f46])).
% 3.80/0.99  
% 3.80/0.99  fof(f79,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f47])).
% 3.80/0.99  
% 3.80/0.99  fof(f83,plain,(
% 3.80/0.99    v2_pre_topc(sK0)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f85,plain,(
% 3.80/0.99    ~v2_struct_0(sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f86,plain,(
% 3.80/0.99    v2_pre_topc(sK1)),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f94,plain,(
% 3.80/0.99    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.80/0.99    inference(cnf_transformation,[],[f59])).
% 3.80/0.99  
% 3.80/0.99  fof(f15,axiom,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f44,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.80/0.99    inference(ennf_transformation,[],[f15])).
% 3.80/0.99  
% 3.80/0.99  fof(f45,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.80/0.99    inference(flattening,[],[f44])).
% 3.80/0.99  
% 3.80/0.99  fof(f54,plain,(
% 3.80/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f45])).
% 3.80/0.99  
% 3.80/0.99  fof(f78,plain,(
% 3.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f54])).
% 3.80/0.99  
% 3.80/0.99  fof(f96,plain,(
% 3.80/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.80/0.99    inference(equality_resolution,[],[f78])).
% 3.80/0.99  
% 3.80/0.99  cnf(c_21,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1090,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_16,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X0)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_265,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_16,c_12]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_266,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_265]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1077,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_23,negated_conjecture,
% 3.80/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1095,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3033,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_23,c_1095]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_29,negated_conjecture,
% 3.80/0.99      ( l1_pre_topc(sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_40,plain,
% 3.80/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_27,negated_conjecture,
% 3.80/0.99      ( m1_pre_topc(sK2,sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1571,plain,
% 3.80/0.99      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 3.80/0.99      inference(resolution,[status(thm)],[c_12,c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1572,plain,
% 3.80/0.99      ( l1_pre_topc(sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3060,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3033,c_40,c_1572]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3061,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_3060]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3068,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1077,c_3061]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3302,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3068,c_40]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3303,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_3302]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3310,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1090,c_3303]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_47,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_49,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_47]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_62,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_64,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.80/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_62]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3057,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.80/0.99      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3033]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3574,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3310,c_40,c_49,c_64,c_1572,c_3057]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_24,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1088,plain,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | v1_partfun1(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | v1_xboole_0(X2)
% 3.80/0.99      | ~ v1_funct_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1102,plain,
% 3.80/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.80/0.99      | v1_partfun1(X0,X1) = iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.80/0.99      | v1_xboole_0(X2) = iProver_top
% 3.80/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4037,plain,
% 3.80/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.80/0.99      | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 3.80/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1088,c_1102]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_34,negated_conjecture,
% 3.80/0.99      ( ~ v2_struct_0(sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_35,plain,
% 3.80/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_26,negated_conjecture,
% 3.80/0.99      ( v1_funct_1(sK3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_43,plain,
% 3.80/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_25,negated_conjecture,
% 3.80/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_44,plain,
% 3.80/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_45,plain,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11,plain,
% 3.80/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_32,negated_conjecture,
% 3.80/0.99      ( l1_pre_topc(sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1461,plain,
% 3.80/0.99      ( l1_struct_0(sK0) ),
% 3.80/0.99      inference(resolution,[status(thm)],[c_11,c_32]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1462,plain,
% 3.80/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1473,plain,
% 3.80/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 3.80/0.99      | v1_partfun1(sK3,X0)
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | ~ v1_funct_1(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1593,plain,
% 3.80/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.80/0.99      | v1_partfun1(sK3,u1_struct_0(sK1))
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 3.80/0.99      | ~ v1_funct_1(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1473]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1594,plain,
% 3.80/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.80/0.99      | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 3.80/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1593]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13,plain,
% 3.80/0.99      ( v2_struct_0(X0)
% 3.80/0.99      | ~ l1_struct_0(X0)
% 3.80/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1817,plain,
% 3.80/0.99      ( v2_struct_0(sK0)
% 3.80/0.99      | ~ l1_struct_0(sK0)
% 3.80/0.99      | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1818,plain,
% 3.80/0.99      ( v2_struct_0(sK0) = iProver_top
% 3.80/0.99      | l1_struct_0(sK0) != iProver_top
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4523,plain,
% 3.80/0.99      ( v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_4037,c_35,c_43,c_44,c_45,c_1462,c_1594,c_1818]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9,plain,
% 3.80/0.99      ( ~ v1_partfun1(X0,X1)
% 3.80/0.99      | ~ v4_relat_1(X0,X1)
% 3.80/0.99      | ~ v1_relat_1(X0)
% 3.80/0.99      | k1_relat_1(X0) = X1 ),
% 3.80/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1100,plain,
% 3.80/0.99      ( k1_relat_1(X0) = X1
% 3.80/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.80/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4528,plain,
% 3.80/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.80/0.99      | v4_relat_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_4523,c_1100]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_478,plain,
% 3.80/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.80/0.99      theory(equality) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_498,plain,
% 3.80/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_478]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_463,plain,( X0 = X0 ),theory(equality) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_506,plain,
% 3.80/0.99      ( sK1 = sK1 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_463]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | v1_relat_1(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1397,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.80/0.99      | v1_relat_1(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4,plain,
% 3.80/0.99      ( v4_relat_1(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1421,plain,
% 3.80/0.99      ( v4_relat_1(sK3,u1_struct_0(sK1))
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1535,plain,
% 3.80/0.99      ( ~ v1_partfun1(sK3,X0)
% 3.80/0.99      | ~ v4_relat_1(sK3,X0)
% 3.80/0.99      | ~ v1_relat_1(sK3)
% 3.80/0.99      | k1_relat_1(sK3) = X0 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1709,plain,
% 3.80/0.99      ( ~ v1_partfun1(sK3,u1_struct_0(sK1))
% 3.80/0.99      | ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 3.80/0.99      | ~ v1_relat_1(sK3)
% 3.80/0.99      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_464,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1933,plain,
% 3.80/0.99      ( X0 != X1 | u1_struct_0(sK1) != X1 | u1_struct_0(sK1) = X0 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_464]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2395,plain,
% 3.80/0.99      ( X0 != u1_struct_0(sK1)
% 3.80/0.99      | u1_struct_0(sK1) = X0
% 3.80/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1933]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3370,plain,
% 3.80/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.80/0.99      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.80/0.99      | k1_relat_1(sK3) != u1_struct_0(sK1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2395]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4960,plain,
% 3.80/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_4528,c_34,c_26,c_25,c_24,c_498,c_506,c_1397,c_1421,
% 3.80/0.99                 c_1461,c_1593,c_1709,c_1817,c_3370]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_20,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1091,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_0,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1108,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.80/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2027,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1091,c_1108]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5025,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,X0) != iProver_top
% 3.80/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_4960,c_2027]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.80/0.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1103,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.80/0.99      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3883,plain,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0)))) = iProver_top
% 3.80/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1088,c_1103]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1104,plain,
% 3.80/0.99      ( v4_relat_1(X0,X1) = iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4311,plain,
% 3.80/0.99      ( v4_relat_1(sK3,X0) = iProver_top
% 3.80/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3883,c_1104]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8479,plain,
% 3.80/0.99      ( m1_pre_topc(sK1,X0) != iProver_top
% 3.80/0.99      | v4_relat_1(sK3,u1_struct_0(X0)) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_5025,c_4311]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1,plain,
% 3.80/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1107,plain,
% 3.80/0.99      ( k7_relat_1(X0,X1) = X0
% 3.80/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9822,plain,
% 3.80/0.99      ( k7_relat_1(sK3,u1_struct_0(X0)) = sK3
% 3.80/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_8479,c_1107]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1398,plain,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.80/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1397]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10554,plain,
% 3.80/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.80/0.99      | k7_relat_1(sK3,u1_struct_0(X0)) = sK3 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_9822,c_45,c_1398]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10555,plain,
% 3.80/0.99      ( k7_relat_1(sK3,u1_struct_0(X0)) = sK3
% 3.80/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_10554]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10564,plain,
% 3.80/0.99      ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK3
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3574,c_10555]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11514,plain,
% 3.80/0.99      ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK3 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_10564,c_40,c_1572]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1085,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5032,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_4960,c_1091]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7182,plain,
% 3.80/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_5032,c_40]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7183,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_7182]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7191,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | r1_tarski(u1_struct_0(X0),k1_relat_1(sK3)) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_7183,c_1108]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.80/0.99      | ~ v1_relat_1(X1)
% 3.80/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.80/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1106,plain,
% 3.80/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.80/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.80/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7516,plain,
% 3.80/0.99      ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(X0))) = u1_struct_0(X0)
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_7191,c_1106]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7532,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | k1_relat_1(k7_relat_1(sK3,u1_struct_0(X0))) = u1_struct_0(X0) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7516,c_45,c_1398]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7533,plain,
% 3.80/0.99      ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(X0))) = u1_struct_0(X0)
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_7532]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7541,plain,
% 3.80/0.99      ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1085,c_7533]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11519,plain,
% 3.80/0.99      ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_11514,c_7541]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1099,plain,
% 3.80/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.80/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3875,plain,
% 3.80/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
% 3.80/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1088,c_1099]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1478,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ v1_funct_1(sK3)
% 3.80/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1596,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.80/0.99      | ~ v1_funct_1(sK3)
% 3.80/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4289,plain,
% 3.80/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3875,c_26,c_24,c_1596]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_19,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.80/0.99      | ~ m1_pre_topc(X3,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.80/0.99      | ~ v2_pre_topc(X2)
% 3.80/0.99      | ~ v2_pre_topc(X1)
% 3.80/0.99      | v2_struct_0(X1)
% 3.80/0.99      | v2_struct_0(X2)
% 3.80/0.99      | ~ l1_pre_topc(X1)
% 3.80/0.99      | ~ l1_pre_topc(X2)
% 3.80/0.99      | ~ v1_funct_1(X0)
% 3.80/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1092,plain,
% 3.80/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.80/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.80/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.80/0.99      | v2_pre_topc(X1) != iProver_top
% 3.80/0.99      | v2_pre_topc(X0) != iProver_top
% 3.80/0.99      | v2_struct_0(X0) = iProver_top
% 3.80/0.99      | v2_struct_0(X1) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2883,plain,
% 3.80/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.80/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.80/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.80/0.99      | v2_struct_0(sK0) = iProver_top
% 3.80/0.99      | v2_struct_0(sK1) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.80/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1088,c_1092]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_33,negated_conjecture,
% 3.80/0.99      ( v2_pre_topc(sK0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_36,plain,
% 3.80/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_37,plain,
% 3.80/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_31,negated_conjecture,
% 3.80/0.99      ( ~ v2_struct_0(sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_38,plain,
% 3.80/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_30,negated_conjecture,
% 3.80/0.99      ( v2_pre_topc(sK1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_39,plain,
% 3.80/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3453,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.80/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_2883,c_35,c_36,c_37,c_38,c_39,c_40,c_43,c_44]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3454,plain,
% 3.80/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.80/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_3453]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3462,plain,
% 3.80/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1085,c_3454]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4294,plain,
% 3.80/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_4289,c_3462]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_22,negated_conjecture,
% 3.80/0.99      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1089,plain,
% 3.80/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4531,plain,
% 3.80/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_4294,c_1089]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4963,plain,
% 3.80/0.99      ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_4960,c_4531]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11520,plain,
% 3.80/0.99      ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_11514,c_4963]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11527,plain,
% 3.80/0.99      ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_11519,c_11520]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_17,plain,
% 3.80/0.99      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.80/0.99      | ~ v1_funct_2(X4,X2,X3)
% 3.80/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.80/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | v1_xboole_0(X3)
% 3.80/0.99      | ~ v1_funct_1(X4) ),
% 3.80/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1520,plain,
% 3.80/0.99      ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
% 3.80/0.99      | ~ v1_funct_2(sK3,X0,X1)
% 3.80/0.99      | ~ v1_funct_2(sK3,X2,X3)
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | v1_xboole_0(X3)
% 3.80/0.99      | ~ v1_funct_1(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4512,plain,
% 3.80/0.99      ( r1_funct_2(X0,X1,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
% 3.80/0.99      | ~ v1_funct_2(sK3,X0,X1)
% 3.80/0.99      | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
% 3.80/0.99      | v1_xboole_0(X1)
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 3.80/0.99      | ~ v1_funct_1(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1520]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8420,plain,
% 3.80/0.99      ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
% 3.80/0.99      | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
% 3.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 3.80/0.99      | ~ v1_funct_1(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_4512]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8430,plain,
% 3.80/0.99      ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) = iProver_top
% 3.80/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.80/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 3.80/0.99      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 3.80/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_8420]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4973,plain,
% 3.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_4960,c_1088]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_472,plain,
% 3.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.99      | v1_funct_2(X3,X4,X5)
% 3.80/0.99      | X5 != X2
% 3.80/0.99      | X3 != X0
% 3.80/0.99      | X4 != X1 ),
% 3.80/0.99      theory(equality) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1483,plain,
% 3.80/0.99      ( v1_funct_2(X0,X1,X2)
% 3.80/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.80/0.99      | X2 != u1_struct_0(sK0)
% 3.80/0.99      | X1 != u1_struct_0(sK1)
% 3.80/0.99      | X0 != sK3 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_472]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1670,plain,
% 3.80/0.99      ( v1_funct_2(sK3,X0,X1)
% 3.80/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.80/0.99      | X1 != u1_struct_0(sK0)
% 3.80/0.99      | X0 != u1_struct_0(sK1)
% 3.80/0.99      | sK3 != sK3 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1483]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2149,plain,
% 3.80/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.80/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),X0)
% 3.80/0.99      | X0 != u1_struct_0(sK0)
% 3.80/0.99      | k1_relat_1(sK3) != u1_struct_0(sK1)
% 3.80/0.99      | sK3 != sK3 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1670]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3181,plain,
% 3.80/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 3.80/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
% 3.80/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.80/0.99      | k1_relat_1(sK3) != u1_struct_0(sK1)
% 3.80/0.99      | sK3 != sK3 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2149]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3184,plain,
% 3.80/0.99      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.80/0.99      | k1_relat_1(sK3) != u1_struct_0(sK1)
% 3.80/0.99      | sK3 != sK3
% 3.80/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.80/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3181]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1784,plain,
% 3.80/0.99      ( u1_struct_0(X0) = u1_struct_0(X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_463]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2327,plain,
% 3.80/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1784]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1587,plain,
% 3.80/0.99      ( sK3 = sK3 ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_463]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(contradiction,plain,
% 3.80/0.99      ( $false ),
% 3.80/0.99      inference(minisat,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_11527,c_8430,c_4973,c_3184,c_2327,c_1818,c_1817,
% 3.80/0.99                 c_1709,c_1593,c_1587,c_1462,c_1461,c_1421,c_1397,c_24,
% 3.80/0.99                 c_44,c_25,c_43,c_26,c_35,c_34]) ).
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  ------                               Statistics
% 3.80/0.99  
% 3.80/0.99  ------ Selected
% 3.80/0.99  
% 3.80/0.99  total_time:                             0.45
% 3.80/0.99  
%------------------------------------------------------------------------------
