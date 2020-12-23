%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:26 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  235 (1040 expanded)
%              Number of clauses        :  141 ( 268 expanded)
%              Number of leaves         :   24 ( 348 expanded)
%              Depth                    :   21
%              Number of atoms          : 1054 (9969 expanded)
%              Number of equality atoms :  365 (1340 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f58,f57,f56,f55])).

fof(f90,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f100,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f82,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f74,plain,(
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

fof(f98,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f95,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1603,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1609,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1613,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3015,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1609,c_1613])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1616,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3796,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_1616])).

cnf(c_4408,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_3796])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_80,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7723,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4408,c_80])).

cnf(c_7724,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7723])).

cnf(c_7732,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_7724])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_57,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_56,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_58,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_12,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_75,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_74,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_76,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_103,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_107,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1877,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1878,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1877])).

cnf(c_1905,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1907,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1905])).

cnf(c_1906,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1905])).

cnf(c_1908,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_911,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1978,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_919,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1939,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_2182,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1939])).

cnf(c_2184,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_2183,plain,
    ( X0 != sK1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_2185,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK1 != sK1
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_1612,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2583,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_1612])).

cnf(c_2584,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2583])).

cnf(c_196,plain,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_12])).

cnf(c_197,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_3508,plain,
    ( m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_3520,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3508])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1607,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X2,X0)
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3586,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,X0,sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_1607])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1606,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2850,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2)
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_1606])).

cnf(c_2851,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK2,sK2)
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2850,c_24])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3175,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2851,c_39,c_40,c_41,c_42])).

cnf(c_3180,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_3175,c_24])).

cnf(c_3633,plain,
    ( k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3586,c_3180])).

cnf(c_3952,plain,
    ( v2_struct_0(X0) = iProver_top
    | k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3633,c_39,c_40,c_41,c_42])).

cnf(c_3953,plain,
    ( k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3952])).

cnf(c_3954,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK1)
    | v2_struct_0(X0)
    | k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3953])).

cnf(c_3956,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | k1_tsep_1(sK1,sK1,sK2) = k1_tsep_1(sK1,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3954])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1608,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k1_tsep_1(X1,X2,X0)
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3682,plain,
    ( k1_tsep_1(X0,X1,sK2) != k1_tsep_1(sK1,sK2,sK2)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3180,c_1608])).

cnf(c_4161,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(X1,sK2) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | k1_tsep_1(X0,X1,sK2) != k1_tsep_1(sK1,sK2,sK2)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3682,c_42])).

cnf(c_4162,plain,
    ( k1_tsep_1(X0,X1,sK2) != k1_tsep_1(sK1,sK2,sK2)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4161])).

cnf(c_4164,plain,
    ( k1_tsep_1(sK1,sK1,sK2) != k1_tsep_1(sK1,sK2,sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4162])).

cnf(c_4175,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4162])).

cnf(c_4176,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4175])).

cnf(c_3524,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4716,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3524])).

cnf(c_2145,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2)
    | X1 != X2
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_3509,plain,
    ( m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_4482,plain,
    ( m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3509])).

cnf(c_6277,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4482])).

cnf(c_7778,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7732,c_32,c_39,c_31,c_40,c_30,c_41,c_29,c_28,c_43,c_24,c_57,c_58,c_75,c_76,c_103,c_107,c_1877,c_1878,c_1907,c_1908,c_1978,c_2184,c_2185,c_2584,c_3520,c_3956,c_4164,c_4176,c_4716,c_6277])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1605,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_572,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_573,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_1593,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_2377,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1593])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_609,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_1592,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_2175,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1605,c_1592])).

cnf(c_2378,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2377,c_2175])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2414,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_36,c_37,c_38,c_39,c_40,c_41,c_45])).

cnf(c_2422,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1603,c_2414])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_477,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_13,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_23,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_497,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_498,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_530,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_477,c_498])).

cnf(c_620,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_27,c_530])).

cnf(c_909,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_620])).

cnf(c_1590,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_2424,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_1590])).

cnf(c_908,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_620])).

cnf(c_1591,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_2271,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1591])).

cnf(c_2442,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2424,c_36,c_38,c_2271])).

cnf(c_2443,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2442])).

cnf(c_7782,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7778,c_2443])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_7,c_6,c_5])).

cnf(c_1594,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_2454,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_1605,c_1594])).

cnf(c_7790,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7782,c_2454])).

cnf(c_7791,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7790])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7791,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 2.87/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.05  
% 2.87/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/1.05  
% 2.87/1.05  ------  iProver source info
% 2.87/1.05  
% 2.87/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.87/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/1.05  git: non_committed_changes: false
% 2.87/1.05  git: last_make_outside_of_git: false
% 2.87/1.05  
% 2.87/1.05  ------ 
% 2.87/1.05  
% 2.87/1.05  ------ Input Options
% 2.87/1.05  
% 2.87/1.05  --out_options                           all
% 2.87/1.05  --tptp_safe_out                         true
% 2.87/1.05  --problem_path                          ""
% 2.87/1.05  --include_path                          ""
% 2.87/1.05  --clausifier                            res/vclausify_rel
% 2.87/1.05  --clausifier_options                    --mode clausify
% 2.87/1.05  --stdin                                 false
% 2.87/1.05  --stats_out                             all
% 2.87/1.05  
% 2.87/1.05  ------ General Options
% 2.87/1.05  
% 2.87/1.05  --fof                                   false
% 2.87/1.05  --time_out_real                         305.
% 2.87/1.05  --time_out_virtual                      -1.
% 2.87/1.05  --symbol_type_check                     false
% 2.87/1.05  --clausify_out                          false
% 2.87/1.05  --sig_cnt_out                           false
% 2.87/1.05  --trig_cnt_out                          false
% 2.87/1.05  --trig_cnt_out_tolerance                1.
% 2.87/1.05  --trig_cnt_out_sk_spl                   false
% 2.87/1.05  --abstr_cl_out                          false
% 2.87/1.05  
% 2.87/1.05  ------ Global Options
% 2.87/1.05  
% 2.87/1.05  --schedule                              default
% 2.87/1.05  --add_important_lit                     false
% 2.87/1.05  --prop_solver_per_cl                    1000
% 2.87/1.05  --min_unsat_core                        false
% 2.87/1.05  --soft_assumptions                      false
% 2.87/1.05  --soft_lemma_size                       3
% 2.87/1.05  --prop_impl_unit_size                   0
% 2.87/1.05  --prop_impl_unit                        []
% 2.87/1.05  --share_sel_clauses                     true
% 2.87/1.05  --reset_solvers                         false
% 2.87/1.05  --bc_imp_inh                            [conj_cone]
% 2.87/1.05  --conj_cone_tolerance                   3.
% 2.87/1.05  --extra_neg_conj                        none
% 2.87/1.05  --large_theory_mode                     true
% 2.87/1.05  --prolific_symb_bound                   200
% 2.87/1.05  --lt_threshold                          2000
% 2.87/1.05  --clause_weak_htbl                      true
% 2.87/1.05  --gc_record_bc_elim                     false
% 2.87/1.05  
% 2.87/1.05  ------ Preprocessing Options
% 2.87/1.05  
% 2.87/1.05  --preprocessing_flag                    true
% 2.87/1.05  --time_out_prep_mult                    0.1
% 2.87/1.05  --splitting_mode                        input
% 2.87/1.05  --splitting_grd                         true
% 2.87/1.05  --splitting_cvd                         false
% 2.87/1.05  --splitting_cvd_svl                     false
% 2.87/1.05  --splitting_nvd                         32
% 2.87/1.05  --sub_typing                            true
% 2.87/1.05  --prep_gs_sim                           true
% 2.87/1.05  --prep_unflatten                        true
% 2.87/1.05  --prep_res_sim                          true
% 2.87/1.05  --prep_upred                            true
% 2.87/1.05  --prep_sem_filter                       exhaustive
% 2.87/1.05  --prep_sem_filter_out                   false
% 2.87/1.05  --pred_elim                             true
% 2.87/1.05  --res_sim_input                         true
% 2.87/1.05  --eq_ax_congr_red                       true
% 2.87/1.05  --pure_diseq_elim                       true
% 2.87/1.05  --brand_transform                       false
% 2.87/1.05  --non_eq_to_eq                          false
% 2.87/1.05  --prep_def_merge                        true
% 2.87/1.05  --prep_def_merge_prop_impl              false
% 2.87/1.05  --prep_def_merge_mbd                    true
% 2.87/1.05  --prep_def_merge_tr_red                 false
% 2.87/1.05  --prep_def_merge_tr_cl                  false
% 2.87/1.05  --smt_preprocessing                     true
% 2.87/1.05  --smt_ac_axioms                         fast
% 2.87/1.05  --preprocessed_out                      false
% 2.87/1.05  --preprocessed_stats                    false
% 2.87/1.05  
% 2.87/1.05  ------ Abstraction refinement Options
% 2.87/1.05  
% 2.87/1.05  --abstr_ref                             []
% 2.87/1.05  --abstr_ref_prep                        false
% 2.87/1.05  --abstr_ref_until_sat                   false
% 2.87/1.05  --abstr_ref_sig_restrict                funpre
% 2.87/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.05  --abstr_ref_under                       []
% 2.87/1.05  
% 2.87/1.05  ------ SAT Options
% 2.87/1.05  
% 2.87/1.05  --sat_mode                              false
% 2.87/1.05  --sat_fm_restart_options                ""
% 2.87/1.05  --sat_gr_def                            false
% 2.87/1.05  --sat_epr_types                         true
% 2.87/1.05  --sat_non_cyclic_types                  false
% 2.87/1.05  --sat_finite_models                     false
% 2.87/1.05  --sat_fm_lemmas                         false
% 2.87/1.05  --sat_fm_prep                           false
% 2.87/1.05  --sat_fm_uc_incr                        true
% 2.87/1.05  --sat_out_model                         small
% 2.87/1.05  --sat_out_clauses                       false
% 2.87/1.05  
% 2.87/1.05  ------ QBF Options
% 2.87/1.05  
% 2.87/1.05  --qbf_mode                              false
% 2.87/1.05  --qbf_elim_univ                         false
% 2.87/1.05  --qbf_dom_inst                          none
% 2.87/1.05  --qbf_dom_pre_inst                      false
% 2.87/1.05  --qbf_sk_in                             false
% 2.87/1.05  --qbf_pred_elim                         true
% 2.87/1.05  --qbf_split                             512
% 2.87/1.05  
% 2.87/1.05  ------ BMC1 Options
% 2.87/1.05  
% 2.87/1.05  --bmc1_incremental                      false
% 2.87/1.05  --bmc1_axioms                           reachable_all
% 2.87/1.05  --bmc1_min_bound                        0
% 2.87/1.05  --bmc1_max_bound                        -1
% 2.87/1.05  --bmc1_max_bound_default                -1
% 2.87/1.05  --bmc1_symbol_reachability              true
% 2.87/1.05  --bmc1_property_lemmas                  false
% 2.87/1.05  --bmc1_k_induction                      false
% 2.87/1.05  --bmc1_non_equiv_states                 false
% 2.87/1.05  --bmc1_deadlock                         false
% 2.87/1.05  --bmc1_ucm                              false
% 2.87/1.05  --bmc1_add_unsat_core                   none
% 2.87/1.05  --bmc1_unsat_core_children              false
% 2.87/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.05  --bmc1_out_stat                         full
% 2.87/1.05  --bmc1_ground_init                      false
% 2.87/1.05  --bmc1_pre_inst_next_state              false
% 2.87/1.05  --bmc1_pre_inst_state                   false
% 2.87/1.05  --bmc1_pre_inst_reach_state             false
% 2.87/1.05  --bmc1_out_unsat_core                   false
% 2.87/1.05  --bmc1_aig_witness_out                  false
% 2.87/1.05  --bmc1_verbose                          false
% 2.87/1.05  --bmc1_dump_clauses_tptp                false
% 2.87/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.05  --bmc1_dump_file                        -
% 2.87/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.05  --bmc1_ucm_extend_mode                  1
% 2.87/1.05  --bmc1_ucm_init_mode                    2
% 2.87/1.05  --bmc1_ucm_cone_mode                    none
% 2.87/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.05  --bmc1_ucm_relax_model                  4
% 2.87/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.05  --bmc1_ucm_layered_model                none
% 2.87/1.05  --bmc1_ucm_max_lemma_size               10
% 2.87/1.05  
% 2.87/1.05  ------ AIG Options
% 2.87/1.05  
% 2.87/1.05  --aig_mode                              false
% 2.87/1.05  
% 2.87/1.05  ------ Instantiation Options
% 2.87/1.05  
% 2.87/1.05  --instantiation_flag                    true
% 2.87/1.05  --inst_sos_flag                         false
% 2.87/1.05  --inst_sos_phase                        true
% 2.87/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.05  --inst_lit_sel_side                     num_symb
% 2.87/1.05  --inst_solver_per_active                1400
% 2.87/1.05  --inst_solver_calls_frac                1.
% 2.87/1.05  --inst_passive_queue_type               priority_queues
% 2.87/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.05  --inst_passive_queues_freq              [25;2]
% 2.87/1.05  --inst_dismatching                      true
% 2.87/1.05  --inst_eager_unprocessed_to_passive     true
% 2.87/1.05  --inst_prop_sim_given                   true
% 2.87/1.05  --inst_prop_sim_new                     false
% 2.87/1.05  --inst_subs_new                         false
% 2.87/1.05  --inst_eq_res_simp                      false
% 2.87/1.05  --inst_subs_given                       false
% 2.87/1.05  --inst_orphan_elimination               true
% 2.87/1.05  --inst_learning_loop_flag               true
% 2.87/1.05  --inst_learning_start                   3000
% 2.87/1.05  --inst_learning_factor                  2
% 2.87/1.05  --inst_start_prop_sim_after_learn       3
% 2.87/1.05  --inst_sel_renew                        solver
% 2.87/1.05  --inst_lit_activity_flag                true
% 2.87/1.05  --inst_restr_to_given                   false
% 2.87/1.05  --inst_activity_threshold               500
% 2.87/1.05  --inst_out_proof                        true
% 2.87/1.05  
% 2.87/1.05  ------ Resolution Options
% 2.87/1.05  
% 2.87/1.05  --resolution_flag                       true
% 2.87/1.05  --res_lit_sel                           adaptive
% 2.87/1.05  --res_lit_sel_side                      none
% 2.87/1.05  --res_ordering                          kbo
% 2.87/1.05  --res_to_prop_solver                    active
% 2.87/1.05  --res_prop_simpl_new                    false
% 2.87/1.05  --res_prop_simpl_given                  true
% 2.87/1.05  --res_passive_queue_type                priority_queues
% 2.87/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.05  --res_passive_queues_freq               [15;5]
% 2.87/1.05  --res_forward_subs                      full
% 2.87/1.05  --res_backward_subs                     full
% 2.87/1.05  --res_forward_subs_resolution           true
% 2.87/1.05  --res_backward_subs_resolution          true
% 2.87/1.05  --res_orphan_elimination                true
% 2.87/1.05  --res_time_limit                        2.
% 2.87/1.05  --res_out_proof                         true
% 2.87/1.05  
% 2.87/1.05  ------ Superposition Options
% 2.87/1.05  
% 2.87/1.05  --superposition_flag                    true
% 2.87/1.05  --sup_passive_queue_type                priority_queues
% 2.87/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.05  --demod_completeness_check              fast
% 2.87/1.05  --demod_use_ground                      true
% 2.87/1.05  --sup_to_prop_solver                    passive
% 2.87/1.05  --sup_prop_simpl_new                    true
% 2.87/1.05  --sup_prop_simpl_given                  true
% 2.87/1.05  --sup_fun_splitting                     false
% 2.87/1.05  --sup_smt_interval                      50000
% 2.87/1.05  
% 2.87/1.05  ------ Superposition Simplification Setup
% 2.87/1.05  
% 2.87/1.05  --sup_indices_passive                   []
% 2.87/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.05  --sup_full_bw                           [BwDemod]
% 2.87/1.05  --sup_immed_triv                        [TrivRules]
% 2.87/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.05  --sup_immed_bw_main                     []
% 2.87/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.05  
% 2.87/1.05  ------ Combination Options
% 2.87/1.05  
% 2.87/1.05  --comb_res_mult                         3
% 2.87/1.05  --comb_sup_mult                         2
% 2.87/1.05  --comb_inst_mult                        10
% 2.87/1.05  
% 2.87/1.05  ------ Debug Options
% 2.87/1.05  
% 2.87/1.05  --dbg_backtrace                         false
% 2.87/1.05  --dbg_dump_prop_clauses                 false
% 2.87/1.05  --dbg_dump_prop_clauses_file            -
% 2.87/1.05  --dbg_out_stat                          false
% 2.87/1.05  ------ Parsing...
% 2.87/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/1.05  
% 2.87/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.87/1.05  
% 2.87/1.05  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/1.05  
% 2.87/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/1.05  ------ Proving...
% 2.87/1.05  ------ Problem Properties 
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  clauses                                 28
% 2.87/1.05  conjectures                             11
% 2.87/1.05  EPR                                     11
% 2.87/1.05  Horn                                    24
% 2.87/1.05  unary                                   12
% 2.87/1.05  binary                                  4
% 2.87/1.05  lits                                    85
% 2.87/1.05  lits eq                                 10
% 2.87/1.05  fd_pure                                 0
% 2.87/1.05  fd_pseudo                               0
% 2.87/1.05  fd_cond                                 0
% 2.87/1.05  fd_pseudo_cond                          1
% 2.87/1.05  AC symbols                              0
% 2.87/1.05  
% 2.87/1.05  ------ Schedule dynamic 5 is on 
% 2.87/1.05  
% 2.87/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  ------ 
% 2.87/1.05  Current options:
% 2.87/1.05  ------ 
% 2.87/1.05  
% 2.87/1.05  ------ Input Options
% 2.87/1.05  
% 2.87/1.05  --out_options                           all
% 2.87/1.05  --tptp_safe_out                         true
% 2.87/1.05  --problem_path                          ""
% 2.87/1.05  --include_path                          ""
% 2.87/1.05  --clausifier                            res/vclausify_rel
% 2.87/1.05  --clausifier_options                    --mode clausify
% 2.87/1.05  --stdin                                 false
% 2.87/1.05  --stats_out                             all
% 2.87/1.05  
% 2.87/1.05  ------ General Options
% 2.87/1.05  
% 2.87/1.05  --fof                                   false
% 2.87/1.05  --time_out_real                         305.
% 2.87/1.05  --time_out_virtual                      -1.
% 2.87/1.05  --symbol_type_check                     false
% 2.87/1.05  --clausify_out                          false
% 2.87/1.05  --sig_cnt_out                           false
% 2.87/1.05  --trig_cnt_out                          false
% 2.87/1.05  --trig_cnt_out_tolerance                1.
% 2.87/1.05  --trig_cnt_out_sk_spl                   false
% 2.87/1.05  --abstr_cl_out                          false
% 2.87/1.05  
% 2.87/1.05  ------ Global Options
% 2.87/1.05  
% 2.87/1.05  --schedule                              default
% 2.87/1.05  --add_important_lit                     false
% 2.87/1.05  --prop_solver_per_cl                    1000
% 2.87/1.05  --min_unsat_core                        false
% 2.87/1.05  --soft_assumptions                      false
% 2.87/1.05  --soft_lemma_size                       3
% 2.87/1.05  --prop_impl_unit_size                   0
% 2.87/1.05  --prop_impl_unit                        []
% 2.87/1.05  --share_sel_clauses                     true
% 2.87/1.05  --reset_solvers                         false
% 2.87/1.05  --bc_imp_inh                            [conj_cone]
% 2.87/1.05  --conj_cone_tolerance                   3.
% 2.87/1.05  --extra_neg_conj                        none
% 2.87/1.05  --large_theory_mode                     true
% 2.87/1.05  --prolific_symb_bound                   200
% 2.87/1.05  --lt_threshold                          2000
% 2.87/1.05  --clause_weak_htbl                      true
% 2.87/1.05  --gc_record_bc_elim                     false
% 2.87/1.05  
% 2.87/1.05  ------ Preprocessing Options
% 2.87/1.05  
% 2.87/1.05  --preprocessing_flag                    true
% 2.87/1.05  --time_out_prep_mult                    0.1
% 2.87/1.05  --splitting_mode                        input
% 2.87/1.05  --splitting_grd                         true
% 2.87/1.05  --splitting_cvd                         false
% 2.87/1.05  --splitting_cvd_svl                     false
% 2.87/1.05  --splitting_nvd                         32
% 2.87/1.05  --sub_typing                            true
% 2.87/1.05  --prep_gs_sim                           true
% 2.87/1.05  --prep_unflatten                        true
% 2.87/1.05  --prep_res_sim                          true
% 2.87/1.05  --prep_upred                            true
% 2.87/1.05  --prep_sem_filter                       exhaustive
% 2.87/1.05  --prep_sem_filter_out                   false
% 2.87/1.05  --pred_elim                             true
% 2.87/1.05  --res_sim_input                         true
% 2.87/1.05  --eq_ax_congr_red                       true
% 2.87/1.05  --pure_diseq_elim                       true
% 2.87/1.05  --brand_transform                       false
% 2.87/1.05  --non_eq_to_eq                          false
% 2.87/1.05  --prep_def_merge                        true
% 2.87/1.05  --prep_def_merge_prop_impl              false
% 2.87/1.05  --prep_def_merge_mbd                    true
% 2.87/1.05  --prep_def_merge_tr_red                 false
% 2.87/1.05  --prep_def_merge_tr_cl                  false
% 2.87/1.05  --smt_preprocessing                     true
% 2.87/1.05  --smt_ac_axioms                         fast
% 2.87/1.05  --preprocessed_out                      false
% 2.87/1.05  --preprocessed_stats                    false
% 2.87/1.05  
% 2.87/1.05  ------ Abstraction refinement Options
% 2.87/1.05  
% 2.87/1.05  --abstr_ref                             []
% 2.87/1.05  --abstr_ref_prep                        false
% 2.87/1.05  --abstr_ref_until_sat                   false
% 2.87/1.05  --abstr_ref_sig_restrict                funpre
% 2.87/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.05  --abstr_ref_under                       []
% 2.87/1.05  
% 2.87/1.05  ------ SAT Options
% 2.87/1.05  
% 2.87/1.05  --sat_mode                              false
% 2.87/1.05  --sat_fm_restart_options                ""
% 2.87/1.05  --sat_gr_def                            false
% 2.87/1.05  --sat_epr_types                         true
% 2.87/1.05  --sat_non_cyclic_types                  false
% 2.87/1.05  --sat_finite_models                     false
% 2.87/1.05  --sat_fm_lemmas                         false
% 2.87/1.05  --sat_fm_prep                           false
% 2.87/1.05  --sat_fm_uc_incr                        true
% 2.87/1.05  --sat_out_model                         small
% 2.87/1.05  --sat_out_clauses                       false
% 2.87/1.05  
% 2.87/1.05  ------ QBF Options
% 2.87/1.05  
% 2.87/1.05  --qbf_mode                              false
% 2.87/1.05  --qbf_elim_univ                         false
% 2.87/1.05  --qbf_dom_inst                          none
% 2.87/1.05  --qbf_dom_pre_inst                      false
% 2.87/1.05  --qbf_sk_in                             false
% 2.87/1.05  --qbf_pred_elim                         true
% 2.87/1.05  --qbf_split                             512
% 2.87/1.05  
% 2.87/1.05  ------ BMC1 Options
% 2.87/1.05  
% 2.87/1.05  --bmc1_incremental                      false
% 2.87/1.05  --bmc1_axioms                           reachable_all
% 2.87/1.05  --bmc1_min_bound                        0
% 2.87/1.05  --bmc1_max_bound                        -1
% 2.87/1.05  --bmc1_max_bound_default                -1
% 2.87/1.05  --bmc1_symbol_reachability              true
% 2.87/1.05  --bmc1_property_lemmas                  false
% 2.87/1.05  --bmc1_k_induction                      false
% 2.87/1.05  --bmc1_non_equiv_states                 false
% 2.87/1.05  --bmc1_deadlock                         false
% 2.87/1.05  --bmc1_ucm                              false
% 2.87/1.05  --bmc1_add_unsat_core                   none
% 2.87/1.05  --bmc1_unsat_core_children              false
% 2.87/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.05  --bmc1_out_stat                         full
% 2.87/1.05  --bmc1_ground_init                      false
% 2.87/1.05  --bmc1_pre_inst_next_state              false
% 2.87/1.05  --bmc1_pre_inst_state                   false
% 2.87/1.05  --bmc1_pre_inst_reach_state             false
% 2.87/1.05  --bmc1_out_unsat_core                   false
% 2.87/1.05  --bmc1_aig_witness_out                  false
% 2.87/1.05  --bmc1_verbose                          false
% 2.87/1.05  --bmc1_dump_clauses_tptp                false
% 2.87/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.05  --bmc1_dump_file                        -
% 2.87/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.05  --bmc1_ucm_extend_mode                  1
% 2.87/1.05  --bmc1_ucm_init_mode                    2
% 2.87/1.05  --bmc1_ucm_cone_mode                    none
% 2.87/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.05  --bmc1_ucm_relax_model                  4
% 2.87/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.05  --bmc1_ucm_layered_model                none
% 2.87/1.05  --bmc1_ucm_max_lemma_size               10
% 2.87/1.05  
% 2.87/1.05  ------ AIG Options
% 2.87/1.05  
% 2.87/1.05  --aig_mode                              false
% 2.87/1.05  
% 2.87/1.05  ------ Instantiation Options
% 2.87/1.05  
% 2.87/1.05  --instantiation_flag                    true
% 2.87/1.05  --inst_sos_flag                         false
% 2.87/1.05  --inst_sos_phase                        true
% 2.87/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.05  --inst_lit_sel_side                     none
% 2.87/1.05  --inst_solver_per_active                1400
% 2.87/1.05  --inst_solver_calls_frac                1.
% 2.87/1.05  --inst_passive_queue_type               priority_queues
% 2.87/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.05  --inst_passive_queues_freq              [25;2]
% 2.87/1.05  --inst_dismatching                      true
% 2.87/1.05  --inst_eager_unprocessed_to_passive     true
% 2.87/1.05  --inst_prop_sim_given                   true
% 2.87/1.05  --inst_prop_sim_new                     false
% 2.87/1.05  --inst_subs_new                         false
% 2.87/1.05  --inst_eq_res_simp                      false
% 2.87/1.05  --inst_subs_given                       false
% 2.87/1.05  --inst_orphan_elimination               true
% 2.87/1.05  --inst_learning_loop_flag               true
% 2.87/1.05  --inst_learning_start                   3000
% 2.87/1.05  --inst_learning_factor                  2
% 2.87/1.05  --inst_start_prop_sim_after_learn       3
% 2.87/1.05  --inst_sel_renew                        solver
% 2.87/1.05  --inst_lit_activity_flag                true
% 2.87/1.05  --inst_restr_to_given                   false
% 2.87/1.05  --inst_activity_threshold               500
% 2.87/1.05  --inst_out_proof                        true
% 2.87/1.05  
% 2.87/1.05  ------ Resolution Options
% 2.87/1.05  
% 2.87/1.05  --resolution_flag                       false
% 2.87/1.05  --res_lit_sel                           adaptive
% 2.87/1.05  --res_lit_sel_side                      none
% 2.87/1.05  --res_ordering                          kbo
% 2.87/1.05  --res_to_prop_solver                    active
% 2.87/1.05  --res_prop_simpl_new                    false
% 2.87/1.05  --res_prop_simpl_given                  true
% 2.87/1.05  --res_passive_queue_type                priority_queues
% 2.87/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.05  --res_passive_queues_freq               [15;5]
% 2.87/1.05  --res_forward_subs                      full
% 2.87/1.05  --res_backward_subs                     full
% 2.87/1.05  --res_forward_subs_resolution           true
% 2.87/1.05  --res_backward_subs_resolution          true
% 2.87/1.05  --res_orphan_elimination                true
% 2.87/1.05  --res_time_limit                        2.
% 2.87/1.05  --res_out_proof                         true
% 2.87/1.05  
% 2.87/1.05  ------ Superposition Options
% 2.87/1.05  
% 2.87/1.05  --superposition_flag                    true
% 2.87/1.05  --sup_passive_queue_type                priority_queues
% 2.87/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.05  --demod_completeness_check              fast
% 2.87/1.05  --demod_use_ground                      true
% 2.87/1.05  --sup_to_prop_solver                    passive
% 2.87/1.05  --sup_prop_simpl_new                    true
% 2.87/1.05  --sup_prop_simpl_given                  true
% 2.87/1.05  --sup_fun_splitting                     false
% 2.87/1.05  --sup_smt_interval                      50000
% 2.87/1.05  
% 2.87/1.05  ------ Superposition Simplification Setup
% 2.87/1.05  
% 2.87/1.05  --sup_indices_passive                   []
% 2.87/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.05  --sup_full_bw                           [BwDemod]
% 2.87/1.05  --sup_immed_triv                        [TrivRules]
% 2.87/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.05  --sup_immed_bw_main                     []
% 2.87/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.05  
% 2.87/1.05  ------ Combination Options
% 2.87/1.05  
% 2.87/1.05  --comb_res_mult                         3
% 2.87/1.05  --comb_sup_mult                         2
% 2.87/1.05  --comb_inst_mult                        10
% 2.87/1.05  
% 2.87/1.05  ------ Debug Options
% 2.87/1.05  
% 2.87/1.05  --dbg_backtrace                         false
% 2.87/1.05  --dbg_dump_prop_clauses                 false
% 2.87/1.05  --dbg_dump_prop_clauses_file            -
% 2.87/1.05  --dbg_out_stat                          false
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  ------ Proving...
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  % SZS status Theorem for theBenchmark.p
% 2.87/1.05  
% 2.87/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/1.05  
% 2.87/1.05  fof(f18,conjecture,(
% 2.87/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f19,negated_conjecture,(
% 2.87/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.87/1.05    inference(negated_conjecture,[],[f18])).
% 2.87/1.05  
% 2.87/1.05  fof(f47,plain,(
% 2.87/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.87/1.05    inference(ennf_transformation,[],[f19])).
% 2.87/1.05  
% 2.87/1.05  fof(f48,plain,(
% 2.87/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.87/1.05    inference(flattening,[],[f47])).
% 2.87/1.05  
% 2.87/1.05  fof(f58,plain,(
% 2.87/1.05    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.87/1.05    introduced(choice_axiom,[])).
% 2.87/1.05  
% 2.87/1.05  fof(f57,plain,(
% 2.87/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.87/1.05    introduced(choice_axiom,[])).
% 2.87/1.05  
% 2.87/1.05  fof(f56,plain,(
% 2.87/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.87/1.05    introduced(choice_axiom,[])).
% 2.87/1.05  
% 2.87/1.05  fof(f55,plain,(
% 2.87/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.87/1.05    introduced(choice_axiom,[])).
% 2.87/1.05  
% 2.87/1.05  fof(f59,plain,(
% 2.87/1.05    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.87/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f58,f57,f56,f55])).
% 2.87/1.05  
% 2.87/1.05  fof(f90,plain,(
% 2.87/1.05    m1_pre_topc(sK2,sK1)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f15,axiom,(
% 2.87/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f42,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(ennf_transformation,[],[f15])).
% 2.87/1.05  
% 2.87/1.05  fof(f79,plain,(
% 2.87/1.05    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f42])).
% 2.87/1.05  
% 2.87/1.05  fof(f2,axiom,(
% 2.87/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f51,plain,(
% 2.87/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.87/1.05    inference(nnf_transformation,[],[f2])).
% 2.87/1.05  
% 2.87/1.05  fof(f63,plain,(
% 2.87/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.87/1.05    inference(cnf_transformation,[],[f51])).
% 2.87/1.05  
% 2.87/1.05  fof(f1,axiom,(
% 2.87/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f49,plain,(
% 2.87/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.87/1.05    inference(nnf_transformation,[],[f1])).
% 2.87/1.05  
% 2.87/1.05  fof(f50,plain,(
% 2.87/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.87/1.05    inference(flattening,[],[f49])).
% 2.87/1.05  
% 2.87/1.05  fof(f62,plain,(
% 2.87/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f50])).
% 2.87/1.05  
% 2.87/1.05  fof(f8,axiom,(
% 2.87/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f30,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(ennf_transformation,[],[f8])).
% 2.87/1.05  
% 2.87/1.05  fof(f70,plain,(
% 2.87/1.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f30])).
% 2.87/1.05  
% 2.87/1.05  fof(f86,plain,(
% 2.87/1.05    ~v2_struct_0(sK1)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f87,plain,(
% 2.87/1.05    v2_pre_topc(sK1)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f88,plain,(
% 2.87/1.05    l1_pre_topc(sK1)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f89,plain,(
% 2.87/1.05    ~v2_struct_0(sK2)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f94,plain,(
% 2.87/1.05    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f14,axiom,(
% 2.87/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f40,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(ennf_transformation,[],[f14])).
% 2.87/1.05  
% 2.87/1.05  fof(f41,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(flattening,[],[f40])).
% 2.87/1.05  
% 2.87/1.05  fof(f53,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(nnf_transformation,[],[f41])).
% 2.87/1.05  
% 2.87/1.05  fof(f77,plain,(
% 2.87/1.05    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f53])).
% 2.87/1.05  
% 2.87/1.05  fof(f100,plain,(
% 2.87/1.05    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 2.87/1.05    inference(equality_resolution,[],[f77])).
% 2.87/1.05  
% 2.87/1.05  fof(f10,axiom,(
% 2.87/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f20,plain,(
% 2.87/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.87/1.05    inference(pure_predicate_removal,[],[f10])).
% 2.87/1.05  
% 2.87/1.05  fof(f33,plain,(
% 2.87/1.05    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.87/1.05    inference(ennf_transformation,[],[f20])).
% 2.87/1.05  
% 2.87/1.05  fof(f34,plain,(
% 2.87/1.05    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.05    inference(flattening,[],[f33])).
% 2.87/1.05  
% 2.87/1.05  fof(f72,plain,(
% 2.87/1.05    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f34])).
% 2.87/1.05  
% 2.87/1.05  fof(f60,plain,(
% 2.87/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.87/1.05    inference(cnf_transformation,[],[f50])).
% 2.87/1.05  
% 2.87/1.05  fof(f97,plain,(
% 2.87/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.87/1.05    inference(equality_resolution,[],[f60])).
% 2.87/1.05  
% 2.87/1.05  fof(f13,axiom,(
% 2.87/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f21,plain,(
% 2.87/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 2.87/1.05    inference(pure_predicate_removal,[],[f13])).
% 2.87/1.05  
% 2.87/1.05  fof(f39,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(ennf_transformation,[],[f21])).
% 2.87/1.05  
% 2.87/1.05  fof(f76,plain,(
% 2.87/1.05    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f39])).
% 2.87/1.05  
% 2.87/1.05  fof(f16,axiom,(
% 2.87/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f43,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.87/1.05    inference(ennf_transformation,[],[f16])).
% 2.87/1.05  
% 2.87/1.05  fof(f44,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.87/1.05    inference(flattening,[],[f43])).
% 2.87/1.05  
% 2.87/1.05  fof(f54,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.87/1.05    inference(nnf_transformation,[],[f44])).
% 2.87/1.05  
% 2.87/1.05  fof(f80,plain,(
% 2.87/1.05    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f54])).
% 2.87/1.05  
% 2.87/1.05  fof(f17,axiom,(
% 2.87/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f45,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.87/1.05    inference(ennf_transformation,[],[f17])).
% 2.87/1.05  
% 2.87/1.05  fof(f46,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.87/1.05    inference(flattening,[],[f45])).
% 2.87/1.05  
% 2.87/1.05  fof(f82,plain,(
% 2.87/1.05    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f46])).
% 2.87/1.05  
% 2.87/1.05  fof(f81,plain,(
% 2.87/1.05    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f54])).
% 2.87/1.05  
% 2.87/1.05  fof(f93,plain,(
% 2.87/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f12,axiom,(
% 2.87/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f37,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.87/1.05    inference(ennf_transformation,[],[f12])).
% 2.87/1.05  
% 2.87/1.05  fof(f38,plain,(
% 2.87/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.87/1.05    inference(flattening,[],[f37])).
% 2.87/1.05  
% 2.87/1.05  fof(f75,plain,(
% 2.87/1.05    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f38])).
% 2.87/1.05  
% 2.87/1.05  fof(f91,plain,(
% 2.87/1.05    v1_funct_1(sK3)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f6,axiom,(
% 2.87/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f27,plain,(
% 2.87/1.05    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.87/1.05    inference(ennf_transformation,[],[f6])).
% 2.87/1.05  
% 2.87/1.05  fof(f28,plain,(
% 2.87/1.05    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.87/1.05    inference(flattening,[],[f27])).
% 2.87/1.05  
% 2.87/1.05  fof(f68,plain,(
% 2.87/1.05    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f28])).
% 2.87/1.05  
% 2.87/1.05  fof(f83,plain,(
% 2.87/1.05    ~v2_struct_0(sK0)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f84,plain,(
% 2.87/1.05    v2_pre_topc(sK0)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f85,plain,(
% 2.87/1.05    l1_pre_topc(sK0)),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f92,plain,(
% 2.87/1.05    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f7,axiom,(
% 2.87/1.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f29,plain,(
% 2.87/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.87/1.05    inference(ennf_transformation,[],[f7])).
% 2.87/1.05  
% 2.87/1.05  fof(f69,plain,(
% 2.87/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f29])).
% 2.87/1.05  
% 2.87/1.05  fof(f9,axiom,(
% 2.87/1.05    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f31,plain,(
% 2.87/1.05    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.87/1.05    inference(ennf_transformation,[],[f9])).
% 2.87/1.05  
% 2.87/1.05  fof(f32,plain,(
% 2.87/1.05    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.05    inference(flattening,[],[f31])).
% 2.87/1.05  
% 2.87/1.05  fof(f71,plain,(
% 2.87/1.05    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f32])).
% 2.87/1.05  
% 2.87/1.05  fof(f11,axiom,(
% 2.87/1.05    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f35,plain,(
% 2.87/1.05    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.87/1.05    inference(ennf_transformation,[],[f11])).
% 2.87/1.05  
% 2.87/1.05  fof(f36,plain,(
% 2.87/1.05    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.87/1.05    inference(flattening,[],[f35])).
% 2.87/1.05  
% 2.87/1.05  fof(f52,plain,(
% 2.87/1.05    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.87/1.05    inference(nnf_transformation,[],[f36])).
% 2.87/1.05  
% 2.87/1.05  fof(f74,plain,(
% 2.87/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f52])).
% 2.87/1.05  
% 2.87/1.05  fof(f98,plain,(
% 2.87/1.05    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.87/1.05    inference(equality_resolution,[],[f74])).
% 2.87/1.05  
% 2.87/1.05  fof(f95,plain,(
% 2.87/1.05    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.87/1.05    inference(cnf_transformation,[],[f59])).
% 2.87/1.05  
% 2.87/1.05  fof(f5,axiom,(
% 2.87/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f22,plain,(
% 2.87/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.87/1.05    inference(pure_predicate_removal,[],[f5])).
% 2.87/1.05  
% 2.87/1.05  fof(f26,plain,(
% 2.87/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.05    inference(ennf_transformation,[],[f22])).
% 2.87/1.05  
% 2.87/1.05  fof(f67,plain,(
% 2.87/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.05    inference(cnf_transformation,[],[f26])).
% 2.87/1.05  
% 2.87/1.05  fof(f3,axiom,(
% 2.87/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f23,plain,(
% 2.87/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.87/1.05    inference(ennf_transformation,[],[f3])).
% 2.87/1.05  
% 2.87/1.05  fof(f24,plain,(
% 2.87/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/1.05    inference(flattening,[],[f23])).
% 2.87/1.05  
% 2.87/1.05  fof(f65,plain,(
% 2.87/1.05    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.87/1.05    inference(cnf_transformation,[],[f24])).
% 2.87/1.05  
% 2.87/1.05  fof(f4,axiom,(
% 2.87/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.87/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.05  
% 2.87/1.05  fof(f25,plain,(
% 2.87/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.05    inference(ennf_transformation,[],[f4])).
% 2.87/1.05  
% 2.87/1.05  fof(f66,plain,(
% 2.87/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.05    inference(cnf_transformation,[],[f25])).
% 2.87/1.05  
% 2.87/1.05  cnf(c_28,negated_conjecture,
% 2.87/1.05      ( m1_pre_topc(sK2,sK1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f90]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1603,plain,
% 2.87/1.05      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_19,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.87/1.05      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.05      | ~ l1_pre_topc(X1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1609,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4,plain,
% 2.87/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f63]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1613,plain,
% 2.87/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.87/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3015,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1609,c_1613]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_0,plain,
% 2.87/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.87/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1616,plain,
% 2.87/1.05      ( X0 = X1
% 2.87/1.05      | r1_tarski(X0,X1) != iProver_top
% 2.87/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3796,plain,
% 2.87/1.05      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_3015,c_1616]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4408,plain,
% 2.87/1.05      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_3015,c_3796]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_10,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_80,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X0) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7723,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | u1_struct_0(X0) = u1_struct_0(X1)
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_4408,c_80]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7724,plain,
% 2.87/1.05      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.87/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(renaming,[status(thm)],[c_7723]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7732,plain,
% 2.87/1.05      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 2.87/1.05      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1603,c_7724]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_32,negated_conjecture,
% 2.87/1.05      ( ~ v2_struct_0(sK1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f86]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_39,plain,
% 2.87/1.05      ( v2_struct_0(sK1) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_31,negated_conjecture,
% 2.87/1.05      ( v2_pre_topc(sK1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_40,plain,
% 2.87/1.05      ( v2_pre_topc(sK1) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_30,negated_conjecture,
% 2.87/1.05      ( l1_pre_topc(sK1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f88]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_41,plain,
% 2.87/1.05      ( l1_pre_topc(sK1) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_29,negated_conjecture,
% 2.87/1.05      ( ~ v2_struct_0(sK2) ),
% 2.87/1.05      inference(cnf_transformation,[],[f89]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_43,plain,
% 2.87/1.05      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_24,negated_conjecture,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.87/1.05      inference(cnf_transformation,[],[f94]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_18,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.87/1.05      | ~ v2_pre_topc(X0)
% 2.87/1.05      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.87/1.05      inference(cnf_transformation,[],[f100]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_57,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 2.87/1.05      | m1_pre_topc(sK1,sK1)
% 2.87/1.05      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.87/1.05      | ~ v2_pre_topc(sK1)
% 2.87/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.87/1.05      | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_18]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_56,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1) = iProver_top
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 2.87/1.05      | v2_pre_topc(X0) != iProver_top
% 2.87/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top
% 2.87/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_58,plain,
% 2.87/1.05      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 2.87/1.05      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.87/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_56]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_12,plain,
% 2.87/1.05      ( ~ v2_pre_topc(X0)
% 2.87/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.87/1.05      | ~ l1_pre_topc(X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f72]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_75,plain,
% 2.87/1.05      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.87/1.05      | ~ v2_pre_topc(sK1)
% 2.87/1.05      | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_12]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_74,plain,
% 2.87/1.05      ( v2_pre_topc(X0) != iProver_top
% 2.87/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_76,plain,
% 2.87/1.05      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_74]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2,plain,
% 2.87/1.05      ( r1_tarski(X0,X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f97]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_103,plain,
% 2.87/1.05      ( r1_tarski(sK1,sK1) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_107,plain,
% 2.87/1.05      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_16,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.87/1.05      | ~ l1_pre_topc(X1) ),
% 2.87/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1877,plain,
% 2.87/1.05      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.87/1.05      | ~ m1_pre_topc(sK2,sK1)
% 2.87/1.05      | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_16]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1878,plain,
% 2.87/1.05      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 2.87/1.05      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_1877]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1905,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1907,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 2.87/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.87/1.05      | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_1905]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1906,plain,
% 2.87/1.05      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_1905]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1908,plain,
% 2.87/1.05      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 2.87/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_1906]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_911,plain,( X0 = X0 ),theory(equality) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1978,plain,
% 2.87/1.05      ( sK2 = sK2 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_911]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_919,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.87/1.05      theory(equality) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1939,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.87/1.05      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | X1 != sK1 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_919]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2182,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 2.87/1.05      | X0 != sK1
% 2.87/1.05      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_1939]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2184,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 2.87/1.05      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | sK1 != sK1 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_2182]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2183,plain,
% 2.87/1.05      ( X0 != sK1
% 2.87/1.05      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2185,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | sK1 != sK1
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_2183]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1612,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X0) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2583,plain,
% 2.87/1.05      ( l1_pre_topc(sK2) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1603,c_1612]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2584,plain,
% 2.87/1.05      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_2583]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_196,plain,
% 2.87/1.05      ( ~ v2_pre_topc(X0)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.87/1.05      | m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_18,c_12]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_197,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 2.87/1.05      | ~ v2_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.87/1.05      inference(renaming,[status(thm)],[c_196]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3508,plain,
% 2.87/1.05      ( m1_pre_topc(X0,sK2)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
% 2.87/1.05      | ~ v2_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.87/1.05      | ~ l1_pre_topc(sK2) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_197]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3520,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
% 2.87/1.05      | m1_pre_topc(sK1,sK2)
% 2.87/1.05      | ~ v2_pre_topc(sK1)
% 2.87/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.87/1.05      | ~ l1_pre_topc(sK2)
% 2.87/1.05      | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_3508]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_21,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ m1_pre_topc(X2,X1)
% 2.87/1.05      | ~ m1_pre_topc(X0,X2)
% 2.87/1.05      | ~ v2_pre_topc(X1)
% 2.87/1.05      | v2_struct_0(X1)
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | v2_struct_0(X2)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
% 2.87/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1607,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X2,X0)
% 2.87/1.05      | m1_pre_topc(X2,X1) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | m1_pre_topc(X2,X0) != iProver_top
% 2.87/1.05      | v2_pre_topc(X1) != iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_struct_0(X2) = iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3586,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,X0,sK2)
% 2.87/1.05      | m1_pre_topc(X0,sK2) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | v2_struct_0(sK2) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1603,c_1607]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_22,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ v2_pre_topc(X1)
% 2.87/1.05      | v2_struct_0(X1)
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f82]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1606,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 2.87/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | v2_pre_topc(X1) != iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2850,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(sK2) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1603,c_1606]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2851,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(sK2) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(demodulation,[status(thm)],[c_2850,c_24]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_42,plain,
% 2.87/1.05      ( v2_struct_0(sK2) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3175,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK1,sK2,sK2) ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_2851,c_39,c_40,c_41,c_42]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3180,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK1,sK2,sK2) ),
% 2.87/1.05      inference(demodulation,[status(thm)],[c_3175,c_24]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3633,plain,
% 2.87/1.05      ( k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | m1_pre_topc(X0,sK2) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | v2_struct_0(sK2) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(demodulation,[status(thm)],[c_3586,c_3180]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3952,plain,
% 2.87/1.05      ( v2_struct_0(X0) = iProver_top
% 2.87/1.05      | k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | m1_pre_topc(X0,sK2) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_3633,c_39,c_40,c_41,c_42]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3953,plain,
% 2.87/1.05      ( k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | m1_pre_topc(X0,sK2) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top ),
% 2.87/1.05      inference(renaming,[status(thm)],[c_3952]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3954,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,sK2)
% 2.87/1.05      | ~ m1_pre_topc(X0,sK1)
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | k1_tsep_1(sK1,X0,sK2) = k1_tsep_1(sK1,sK2,sK2) ),
% 2.87/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_3953]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3956,plain,
% 2.87/1.05      ( ~ m1_pre_topc(sK1,sK2)
% 2.87/1.05      | ~ m1_pre_topc(sK1,sK1)
% 2.87/1.05      | v2_struct_0(sK1)
% 2.87/1.05      | k1_tsep_1(sK1,sK1,sK2) = k1_tsep_1(sK1,sK2,sK2) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_3954]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_20,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ m1_pre_topc(X2,X1)
% 2.87/1.05      | m1_pre_topc(X0,X2)
% 2.87/1.05      | ~ v2_pre_topc(X1)
% 2.87/1.05      | v2_struct_0(X1)
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | v2_struct_0(X2)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X1,X0,X2) ),
% 2.87/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1608,plain,
% 2.87/1.05      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k1_tsep_1(X1,X2,X0)
% 2.87/1.05      | m1_pre_topc(X2,X1) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.87/1.05      | m1_pre_topc(X2,X0) = iProver_top
% 2.87/1.05      | v2_pre_topc(X1) != iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_struct_0(X2) = iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3682,plain,
% 2.87/1.05      ( k1_tsep_1(X0,X1,sK2) != k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | m1_pre_topc(X1,sK2) = iProver_top
% 2.87/1.05      | m1_pre_topc(sK2,X0) != iProver_top
% 2.87/1.05      | v2_pre_topc(X0) != iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | v2_struct_0(sK2) = iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_3180,c_1608]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4161,plain,
% 2.87/1.05      ( v2_struct_0(X0) = iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_pre_topc(X0) != iProver_top
% 2.87/1.05      | m1_pre_topc(sK2,X0) != iProver_top
% 2.87/1.05      | m1_pre_topc(X1,sK2) = iProver_top
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | k1_tsep_1(X0,X1,sK2) != k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_3682,c_42]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4162,plain,
% 2.87/1.05      ( k1_tsep_1(X0,X1,sK2) != k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.87/1.05      | m1_pre_topc(X1,sK2) = iProver_top
% 2.87/1.05      | m1_pre_topc(sK2,X0) != iProver_top
% 2.87/1.05      | v2_pre_topc(X0) != iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.87/1.05      inference(renaming,[status(thm)],[c_4161]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4164,plain,
% 2.87/1.05      ( k1_tsep_1(sK1,sK1,sK2) != k1_tsep_1(sK1,sK2,sK2)
% 2.87/1.05      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.87/1.05      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.87/1.05      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_4162]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4175,plain,
% 2.87/1.05      ( m1_pre_topc(sK2,sK2) = iProver_top
% 2.87/1.05      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(sK2) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(equality_resolution,[status(thm)],[c_4162]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4176,plain,
% 2.87/1.05      ( m1_pre_topc(sK2,sK2)
% 2.87/1.05      | ~ m1_pre_topc(sK2,sK1)
% 2.87/1.05      | ~ v2_pre_topc(sK1)
% 2.87/1.05      | v2_struct_0(sK2)
% 2.87/1.05      | v2_struct_0(sK1)
% 2.87/1.05      | ~ l1_pre_topc(sK1) ),
% 2.87/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_4175]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3524,plain,
% 2.87/1.05      ( ~ m1_pre_topc(X0,sK2)
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
% 2.87/1.05      | ~ l1_pre_topc(sK2) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_16]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4716,plain,
% 2.87/1.05      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 2.87/1.05      | ~ m1_pre_topc(sK2,sK2)
% 2.87/1.05      | ~ l1_pre_topc(sK2) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_3524]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2145,plain,
% 2.87/1.05      ( m1_pre_topc(X0,X1)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2)
% 2.87/1.05      | X1 != X2
% 2.87/1.05      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_919]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_3509,plain,
% 2.87/1.05      ( m1_pre_topc(X0,sK2)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)
% 2.87/1.05      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | sK2 != X1 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_2145]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_4482,plain,
% 2.87/1.05      ( m1_pre_topc(X0,sK2)
% 2.87/1.05      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 2.87/1.05      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | sK2 != sK2 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_3509]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_6277,plain,
% 2.87/1.05      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 2.87/1.05      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
% 2.87/1.05      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 2.87/1.05      | sK2 != sK2 ),
% 2.87/1.05      inference(instantiation,[status(thm)],[c_4482]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7778,plain,
% 2.87/1.05      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_7732,c_32,c_39,c_31,c_40,c_30,c_41,c_29,c_28,c_43,
% 2.87/1.05                 c_24,c_57,c_58,c_75,c_76,c_103,c_107,c_1877,c_1878,
% 2.87/1.05                 c_1907,c_1908,c_1978,c_2184,c_2185,c_2584,c_3520,c_3956,
% 2.87/1.05                 c_4164,c_4176,c_4716,c_6277]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_25,negated_conjecture,
% 2.87/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 2.87/1.05      inference(cnf_transformation,[],[f93]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1605,plain,
% 2.87/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_15,plain,
% 2.87/1.05      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.87/1.05      | ~ m1_pre_topc(X3,X1)
% 2.87/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.87/1.05      | ~ v2_pre_topc(X1)
% 2.87/1.05      | ~ v2_pre_topc(X2)
% 2.87/1.05      | v2_struct_0(X1)
% 2.87/1.05      | v2_struct_0(X2)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | ~ l1_pre_topc(X2)
% 2.87/1.05      | ~ v1_funct_1(X0)
% 2.87/1.05      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.87/1.05      inference(cnf_transformation,[],[f75]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_27,negated_conjecture,
% 2.87/1.05      ( v1_funct_1(sK3) ),
% 2.87/1.05      inference(cnf_transformation,[],[f91]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_572,plain,
% 2.87/1.05      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.87/1.05      | ~ m1_pre_topc(X3,X1)
% 2.87/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.87/1.05      | ~ v2_pre_topc(X1)
% 2.87/1.05      | ~ v2_pre_topc(X2)
% 2.87/1.05      | v2_struct_0(X1)
% 2.87/1.05      | v2_struct_0(X2)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | ~ l1_pre_topc(X2)
% 2.87/1.05      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.87/1.05      | sK3 != X0 ),
% 2.87/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_573,plain,
% 2.87/1.05      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 2.87/1.05      | ~ m1_pre_topc(X2,X0)
% 2.87/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.87/1.05      | ~ v2_pre_topc(X0)
% 2.87/1.05      | ~ v2_pre_topc(X1)
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | v2_struct_0(X1)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | ~ l1_pre_topc(X1)
% 2.87/1.05      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 2.87/1.05      inference(unflattening,[status(thm)],[c_572]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1593,plain,
% 2.87/1.05      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 2.87/1.05      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.87/1.05      | m1_pre_topc(X2,X0) != iProver_top
% 2.87/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.87/1.05      | v2_pre_topc(X1) != iProver_top
% 2.87/1.05      | v2_pre_topc(X0) != iProver_top
% 2.87/1.05      | v2_struct_0(X1) = iProver_top
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | l1_pre_topc(X1) != iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2377,plain,
% 2.87/1.05      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 2.87/1.05      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK0) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(sK0) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK0) != iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1605,c_1593]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_8,plain,
% 2.87/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.05      | ~ v1_funct_1(X0)
% 2.87/1.05      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.87/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_608,plain,
% 2.87/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.05      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.87/1.05      | sK3 != X0 ),
% 2.87/1.05      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_609,plain,
% 2.87/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/1.05      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 2.87/1.05      inference(unflattening,[status(thm)],[c_608]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1592,plain,
% 2.87/1.05      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 2.87/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2175,plain,
% 2.87/1.05      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1605,c_1592]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2378,plain,
% 2.87/1.05      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 2.87/1.05      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK0) != iProver_top
% 2.87/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.87/1.05      | v2_struct_0(sK0) = iProver_top
% 2.87/1.05      | v2_struct_0(sK1) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK0) != iProver_top
% 2.87/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.87/1.05      inference(demodulation,[status(thm)],[c_2377,c_2175]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_35,negated_conjecture,
% 2.87/1.05      ( ~ v2_struct_0(sK0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f83]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_36,plain,
% 2.87/1.05      ( v2_struct_0(sK0) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_34,negated_conjecture,
% 2.87/1.05      ( v2_pre_topc(sK0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f84]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_37,plain,
% 2.87/1.05      ( v2_pre_topc(sK0) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_33,negated_conjecture,
% 2.87/1.05      ( l1_pre_topc(sK0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f85]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_38,plain,
% 2.87/1.05      ( l1_pre_topc(sK0) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_26,negated_conjecture,
% 2.87/1.05      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 2.87/1.05      inference(cnf_transformation,[],[f92]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_45,plain,
% 2.87/1.05      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2414,plain,
% 2.87/1.05      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 2.87/1.05      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_2378,c_36,c_37,c_38,c_39,c_40,c_41,c_45]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2422,plain,
% 2.87/1.05      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1603,c_2414]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_9,plain,
% 2.87/1.05      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_11,plain,
% 2.87/1.05      ( v2_struct_0(X0)
% 2.87/1.05      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.87/1.05      | ~ l1_struct_0(X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f71]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_477,plain,
% 2.87/1.05      ( v2_struct_0(X0)
% 2.87/1.05      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.87/1.05      | ~ l1_pre_topc(X0) ),
% 2.87/1.05      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_13,plain,
% 2.87/1.05      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.87/1.05      | ~ v1_funct_2(X4,X2,X3)
% 2.87/1.05      | ~ v1_funct_2(X4,X0,X1)
% 2.87/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.87/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/1.05      | v1_xboole_0(X1)
% 2.87/1.05      | v1_xboole_0(X3)
% 2.87/1.05      | ~ v1_funct_1(X4) ),
% 2.87/1.05      inference(cnf_transformation,[],[f98]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_23,negated_conjecture,
% 2.87/1.05      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 2.87/1.05      inference(cnf_transformation,[],[f95]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_497,plain,
% 2.87/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/1.05      | ~ v1_funct_2(X0,X3,X4)
% 2.87/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.87/1.05      | v1_xboole_0(X4)
% 2.87/1.05      | v1_xboole_0(X2)
% 2.87/1.05      | ~ v1_funct_1(X0)
% 2.87/1.05      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 2.87/1.05      | u1_struct_0(sK2) != X1
% 2.87/1.05      | u1_struct_0(sK0) != X2
% 2.87/1.05      | u1_struct_0(sK0) != X4
% 2.87/1.05      | u1_struct_0(sK1) != X3
% 2.87/1.05      | sK3 != X0 ),
% 2.87/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_498,plain,
% 2.87/1.05      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.87/1.05      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.87/1.05      | v1_xboole_0(u1_struct_0(sK0))
% 2.87/1.05      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.87/1.05      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.87/1.05      inference(unflattening,[status(thm)],[c_497]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_530,plain,
% 2.87/1.05      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.87/1.05      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.87/1.05      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.87/1.05      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.87/1.05      inference(resolution_lifted,[status(thm)],[c_477,c_498]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_620,plain,
% 2.87/1.05      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.87/1.05      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.87/1.05      | v2_struct_0(X0)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.87/1.05      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.87/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_530]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_909,plain,
% 2.87/1.05      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.87/1.05      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.87/1.05      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.87/1.05      | sP0_iProver_split
% 2.87/1.05      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 2.87/1.05      inference(splitting,
% 2.87/1.05                [splitting(split),new_symbols(definition,[])],
% 2.87/1.05                [c_620]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1590,plain,
% 2.87/1.05      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.87/1.05      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | sP0_iProver_split = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2424,plain,
% 2.87/1.05      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | sP0_iProver_split = iProver_top ),
% 2.87/1.05      inference(demodulation,[status(thm)],[c_2422,c_1590]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_908,plain,
% 2.87/1.05      ( v2_struct_0(X0)
% 2.87/1.05      | ~ l1_pre_topc(X0)
% 2.87/1.05      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.87/1.05      | ~ sP0_iProver_split ),
% 2.87/1.05      inference(splitting,
% 2.87/1.05                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.87/1.05                [c_620]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1591,plain,
% 2.87/1.05      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.87/1.05      | v2_struct_0(X0) = iProver_top
% 2.87/1.05      | l1_pre_topc(X0) != iProver_top
% 2.87/1.05      | sP0_iProver_split != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2271,plain,
% 2.87/1.05      ( v2_struct_0(sK0) = iProver_top
% 2.87/1.05      | l1_pre_topc(sK0) != iProver_top
% 2.87/1.05      | sP0_iProver_split != iProver_top ),
% 2.87/1.05      inference(equality_resolution,[status(thm)],[c_1591]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2442,plain,
% 2.87/1.05      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_2424,c_36,c_38,c_2271]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2443,plain,
% 2.87/1.05      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.87/1.05      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.87/1.05      inference(renaming,[status(thm)],[c_2442]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7782,plain,
% 2.87/1.05      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 2.87/1.05      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.87/1.05      inference(demodulation,[status(thm)],[c_7778,c_2443]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7,plain,
% 2.87/1.05      ( v4_relat_1(X0,X1)
% 2.87/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.87/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_5,plain,
% 2.87/1.05      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.87/1.05      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_457,plain,
% 2.87/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.05      | ~ v1_relat_1(X0)
% 2.87/1.05      | k7_relat_1(X0,X1) = X0 ),
% 2.87/1.05      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_6,plain,
% 2.87/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.05      | v1_relat_1(X0) ),
% 2.87/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_461,plain,
% 2.87/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.05      | k7_relat_1(X0,X1) = X0 ),
% 2.87/1.05      inference(global_propositional_subsumption,
% 2.87/1.05                [status(thm)],
% 2.87/1.05                [c_457,c_7,c_6,c_5]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_1594,plain,
% 2.87/1.05      ( k7_relat_1(X0,X1) = X0
% 2.87/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_2454,plain,
% 2.87/1.05      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 2.87/1.05      inference(superposition,[status(thm)],[c_1605,c_1594]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7790,plain,
% 2.87/1.05      ( sK3 != sK3
% 2.87/1.05      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.87/1.05      inference(light_normalisation,[status(thm)],[c_7782,c_2454]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_7791,plain,
% 2.87/1.05      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.87/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.87/1.05      inference(equality_resolution_simp,[status(thm)],[c_7790]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(c_46,plain,
% 2.87/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.87/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.87/1.05  
% 2.87/1.05  cnf(contradiction,plain,
% 2.87/1.05      ( $false ),
% 2.87/1.05      inference(minisat,[status(thm)],[c_7791,c_46,c_45]) ).
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.05  
% 2.87/1.05  ------                               Statistics
% 2.87/1.05  
% 2.87/1.05  ------ General
% 2.87/1.05  
% 2.87/1.05  abstr_ref_over_cycles:                  0
% 2.87/1.05  abstr_ref_under_cycles:                 0
% 2.87/1.05  gc_basic_clause_elim:                   0
% 2.87/1.05  forced_gc_time:                         0
% 2.87/1.05  parsing_time:                           0.009
% 2.87/1.05  unif_index_cands_time:                  0.
% 2.87/1.05  unif_index_add_time:                    0.
% 2.87/1.05  orderings_time:                         0.
% 2.87/1.05  out_proof_time:                         0.042
% 2.87/1.05  total_time:                             0.337
% 2.87/1.05  num_of_symbols:                         58
% 2.87/1.05  num_of_terms:                           4806
% 2.87/1.05  
% 2.87/1.05  ------ Preprocessing
% 2.87/1.05  
% 2.87/1.05  num_of_splits:                          1
% 2.87/1.05  num_of_split_atoms:                     1
% 2.87/1.05  num_of_reused_defs:                     0
% 2.87/1.05  num_eq_ax_congr_red:                    24
% 2.87/1.05  num_of_sem_filtered_clauses:            1
% 2.87/1.05  num_of_subtypes:                        0
% 2.87/1.05  monotx_restored_types:                  0
% 2.87/1.05  sat_num_of_epr_types:                   0
% 2.87/1.05  sat_num_of_non_cyclic_types:            0
% 2.87/1.05  sat_guarded_non_collapsed_types:        0
% 2.87/1.05  num_pure_diseq_elim:                    0
% 2.87/1.05  simp_replaced_by:                       0
% 2.87/1.05  res_preprocessed:                       150
% 2.87/1.05  prep_upred:                             0
% 2.87/1.05  prep_unflattend:                        13
% 2.87/1.05  smt_new_axioms:                         0
% 2.87/1.05  pred_elim_cands:                        7
% 2.87/1.05  pred_elim:                              6
% 2.87/1.05  pred_elim_cl:                           7
% 2.87/1.05  pred_elim_cycles:                       8
% 2.87/1.05  merged_defs:                            8
% 2.87/1.05  merged_defs_ncl:                        0
% 2.87/1.05  bin_hyper_res:                          8
% 2.87/1.05  prep_cycles:                            4
% 2.87/1.05  pred_elim_time:                         0.007
% 2.87/1.05  splitting_time:                         0.
% 2.87/1.05  sem_filter_time:                        0.
% 2.87/1.05  monotx_time:                            0.
% 2.87/1.05  subtype_inf_time:                       0.
% 2.87/1.05  
% 2.87/1.05  ------ Problem properties
% 2.87/1.05  
% 2.87/1.05  clauses:                                28
% 2.87/1.05  conjectures:                            11
% 2.87/1.05  epr:                                    11
% 2.87/1.05  horn:                                   24
% 2.87/1.05  ground:                                 12
% 2.87/1.05  unary:                                  12
% 2.87/1.05  binary:                                 4
% 2.87/1.05  lits:                                   85
% 2.87/1.05  lits_eq:                                10
% 2.87/1.05  fd_pure:                                0
% 2.87/1.05  fd_pseudo:                              0
% 2.87/1.05  fd_cond:                                0
% 2.87/1.05  fd_pseudo_cond:                         1
% 2.87/1.05  ac_symbols:                             0
% 2.87/1.05  
% 2.87/1.05  ------ Propositional Solver
% 2.87/1.05  
% 2.87/1.05  prop_solver_calls:                      29
% 2.87/1.05  prop_fast_solver_calls:                 1575
% 2.87/1.05  smt_solver_calls:                       0
% 2.87/1.05  smt_fast_solver_calls:                  0
% 2.87/1.05  prop_num_of_clauses:                    2141
% 2.87/1.05  prop_preprocess_simplified:             6688
% 2.87/1.05  prop_fo_subsumed:                       99
% 2.87/1.05  prop_solver_time:                       0.
% 2.87/1.05  smt_solver_time:                        0.
% 2.87/1.05  smt_fast_solver_time:                   0.
% 2.87/1.05  prop_fast_solver_time:                  0.
% 2.87/1.05  prop_unsat_core_time:                   0.
% 2.87/1.05  
% 2.87/1.05  ------ QBF
% 2.87/1.05  
% 2.87/1.05  qbf_q_res:                              0
% 2.87/1.05  qbf_num_tautologies:                    0
% 2.87/1.05  qbf_prep_cycles:                        0
% 2.87/1.05  
% 2.87/1.05  ------ BMC1
% 2.87/1.05  
% 2.87/1.05  bmc1_current_bound:                     -1
% 2.87/1.05  bmc1_last_solved_bound:                 -1
% 2.87/1.05  bmc1_unsat_core_size:                   -1
% 2.87/1.05  bmc1_unsat_core_parents_size:           -1
% 2.87/1.05  bmc1_merge_next_fun:                    0
% 2.87/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.05  
% 2.87/1.05  ------ Instantiation
% 2.87/1.05  
% 2.87/1.05  inst_num_of_clauses:                    690
% 2.87/1.05  inst_num_in_passive:                    29
% 2.87/1.05  inst_num_in_active:                     493
% 2.87/1.05  inst_num_in_unprocessed:                168
% 2.87/1.05  inst_num_of_loops:                      520
% 2.87/1.05  inst_num_of_learning_restarts:          0
% 2.87/1.05  inst_num_moves_active_passive:          23
% 2.87/1.05  inst_lit_activity:                      0
% 2.87/1.05  inst_lit_activity_moves:                0
% 2.87/1.05  inst_num_tautologies:                   0
% 2.87/1.05  inst_num_prop_implied:                  0
% 2.87/1.05  inst_num_existing_simplified:           0
% 2.87/1.05  inst_num_eq_res_simplified:             0
% 2.87/1.05  inst_num_child_elim:                    0
% 2.87/1.05  inst_num_of_dismatching_blockings:      451
% 2.87/1.05  inst_num_of_non_proper_insts:           1165
% 2.87/1.05  inst_num_of_duplicates:                 0
% 2.87/1.05  inst_inst_num_from_inst_to_res:         0
% 2.87/1.05  inst_dismatching_checking_time:         0.
% 2.87/1.05  
% 2.87/1.05  ------ Resolution
% 2.87/1.05  
% 2.87/1.05  res_num_of_clauses:                     0
% 2.87/1.05  res_num_in_passive:                     0
% 2.87/1.05  res_num_in_active:                      0
% 2.87/1.05  res_num_of_loops:                       154
% 2.87/1.05  res_forward_subset_subsumed:            170
% 2.87/1.05  res_backward_subset_subsumed:           6
% 2.87/1.05  res_forward_subsumed:                   0
% 2.87/1.05  res_backward_subsumed:                  0
% 2.87/1.05  res_forward_subsumption_resolution:     0
% 2.87/1.05  res_backward_subsumption_resolution:    0
% 2.87/1.05  res_clause_to_clause_subsumption:       598
% 2.87/1.05  res_orphan_elimination:                 0
% 2.87/1.05  res_tautology_del:                      170
% 2.87/1.05  res_num_eq_res_simplified:              0
% 2.87/1.05  res_num_sel_changes:                    0
% 2.87/1.05  res_moves_from_active_to_pass:          0
% 2.87/1.05  
% 2.87/1.05  ------ Superposition
% 2.87/1.05  
% 2.87/1.05  sup_time_total:                         0.
% 2.87/1.05  sup_time_generating:                    0.
% 2.87/1.05  sup_time_sim_full:                      0.
% 2.87/1.05  sup_time_sim_immed:                     0.
% 2.87/1.05  
% 2.87/1.05  sup_num_of_clauses:                     121
% 2.87/1.05  sup_num_in_active:                      83
% 2.87/1.05  sup_num_in_passive:                     38
% 2.87/1.05  sup_num_of_loops:                       103
% 2.87/1.05  sup_fw_superposition:                   106
% 2.87/1.05  sup_bw_superposition:                   70
% 2.87/1.05  sup_immediate_simplified:               63
% 2.87/1.05  sup_given_eliminated:                   0
% 2.87/1.05  comparisons_done:                       0
% 2.87/1.05  comparisons_avoided:                    0
% 2.87/1.05  
% 2.87/1.05  ------ Simplifications
% 2.87/1.05  
% 2.87/1.05  
% 2.87/1.05  sim_fw_subset_subsumed:                 21
% 2.87/1.05  sim_bw_subset_subsumed:                 7
% 2.87/1.05  sim_fw_subsumed:                        11
% 2.87/1.05  sim_bw_subsumed:                        0
% 2.87/1.05  sim_fw_subsumption_res:                 1
% 2.87/1.05  sim_bw_subsumption_res:                 0
% 2.87/1.05  sim_tautology_del:                      8
% 2.87/1.05  sim_eq_tautology_del:                   7
% 2.87/1.05  sim_eq_res_simp:                        1
% 2.87/1.05  sim_fw_demodulated:                     6
% 2.87/1.05  sim_bw_demodulated:                     20
% 2.87/1.05  sim_light_normalised:                   44
% 2.87/1.05  sim_joinable_taut:                      0
% 2.87/1.05  sim_joinable_simp:                      0
% 2.87/1.05  sim_ac_normalised:                      0
% 2.87/1.05  sim_smt_subsumption:                    0
% 2.87/1.05  
%------------------------------------------------------------------------------
