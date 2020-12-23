%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:29 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 559 expanded)
%              Number of clauses        :  109 ( 173 expanded)
%              Number of leaves         :   23 ( 170 expanded)
%              Depth                    :   20
%              Number of atoms          :  742 (4620 expanded)
%              Number of equality atoms :  218 ( 618 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f51,f50,f49,f48])).

fof(f83,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f88,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1663,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1667,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3893,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_1672])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1675,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6133,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3893,c_1675])).

cnf(c_6622,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3893,c_6133])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_71,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3759,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_21,c_4])).

cnf(c_3760,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3759])).

cnf(c_8813,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6622,c_71,c_3760,c_6133])).

cnf(c_8814,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8813])).

cnf(c_8823,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_8814])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_48,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_50,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_63,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_65,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_2380,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_13,c_28])).

cnf(c_2381,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1668,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4051,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1668])).

cnf(c_4066,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4051])).

cnf(c_8963,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8823,c_41,c_50,c_65,c_2381,c_4066])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1665,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_566,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_567,plain,
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
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_1652,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_2458,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1652])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_603,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_1651,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2355,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1665,c_1651])).

cnf(c_2459,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2458,c_2355])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2595,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2459,c_36,c_37,c_38,c_39,c_40,c_41,c_45])).

cnf(c_2603,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1663,c_2595])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_452,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_12,c_14])).

cnf(c_18,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_23,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_491,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_492,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_524,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_452,c_492])).

cnf(c_614,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_27,c_524])).

cnf(c_903,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | sP0_iProver_split
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_614])).

cnf(c_1649,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_2605,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2603,c_1649])).

cnf(c_902,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_614])).

cnf(c_905,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2173,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_902,c_905])).

cnf(c_2174,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_2733,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2605,c_36,c_38,c_2174])).

cnf(c_2734,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2733])).

cnf(c_8972,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8963,c_2734])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_1653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_2746,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1653])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2175,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2240,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_2241,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_261,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_331,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_261])).

cnf(c_2024,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_2576,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_2577,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2576])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3020,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3021,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3020])).

cnf(c_3294,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_46,c_2241,c_2577,c_3021])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1670,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3876,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_1670])).

cnf(c_4953,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3876,c_46,c_2241,c_2577,c_3021])).

cnf(c_8983,plain,
    ( sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8972,c_4953])).

cnf(c_8984,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8983])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8984,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.31/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.03  
% 3.31/1.03  ------  iProver source info
% 3.31/1.03  
% 3.31/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.03  git: non_committed_changes: false
% 3.31/1.03  git: last_make_outside_of_git: false
% 3.31/1.03  
% 3.31/1.03  ------ 
% 3.31/1.03  ------ Parsing...
% 3.31/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.03  ------ Proving...
% 3.31/1.03  ------ Problem Properties 
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  clauses                                 28
% 3.31/1.03  conjectures                             11
% 3.31/1.03  EPR                                     13
% 3.31/1.03  Horn                                    27
% 3.31/1.03  unary                                   13
% 3.31/1.03  binary                                  4
% 3.31/1.03  lits                                    65
% 3.31/1.03  lits eq                                 7
% 3.31/1.03  fd_pure                                 0
% 3.31/1.03  fd_pseudo                               0
% 3.31/1.03  fd_cond                                 0
% 3.31/1.03  fd_pseudo_cond                          1
% 3.31/1.03  AC symbols                              0
% 3.31/1.03  
% 3.31/1.03  ------ Input Options Time Limit: Unbounded
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  ------ 
% 3.31/1.03  Current options:
% 3.31/1.03  ------ 
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  ------ Proving...
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  % SZS status Theorem for theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  fof(f18,conjecture,(
% 3.31/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f19,negated_conjecture,(
% 3.31/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 3.31/1.03    inference(negated_conjecture,[],[f18])).
% 3.31/1.03  
% 3.31/1.03  fof(f40,plain,(
% 3.31/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.31/1.03    inference(ennf_transformation,[],[f19])).
% 3.31/1.03  
% 3.31/1.03  fof(f41,plain,(
% 3.31/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.31/1.03    inference(flattening,[],[f40])).
% 3.31/1.03  
% 3.31/1.03  fof(f51,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.31/1.03    introduced(choice_axiom,[])).
% 3.31/1.03  
% 3.31/1.03  fof(f50,plain,(
% 3.31/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 3.31/1.03    introduced(choice_axiom,[])).
% 3.31/1.03  
% 3.31/1.03  fof(f49,plain,(
% 3.31/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.31/1.03    introduced(choice_axiom,[])).
% 3.31/1.03  
% 3.31/1.03  fof(f48,plain,(
% 3.31/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.31/1.03    introduced(choice_axiom,[])).
% 3.31/1.03  
% 3.31/1.03  fof(f52,plain,(
% 3.31/1.03    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.31/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f51,f50,f49,f48])).
% 3.31/1.03  
% 3.31/1.03  fof(f83,plain,(
% 3.31/1.03    m1_pre_topc(sK2,sK1)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f16,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f38,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f16])).
% 3.31/1.03  
% 3.31/1.03  fof(f74,plain,(
% 3.31/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f38])).
% 3.31/1.03  
% 3.31/1.03  fof(f2,axiom,(
% 3.31/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f44,plain,(
% 3.31/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.31/1.03    inference(nnf_transformation,[],[f2])).
% 3.31/1.03  
% 3.31/1.03  fof(f56,plain,(
% 3.31/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f44])).
% 3.31/1.03  
% 3.31/1.03  fof(f1,axiom,(
% 3.31/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f42,plain,(
% 3.31/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.03    inference(nnf_transformation,[],[f1])).
% 3.31/1.03  
% 3.31/1.03  fof(f43,plain,(
% 3.31/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.03    inference(flattening,[],[f42])).
% 3.31/1.03  
% 3.31/1.03  fof(f55,plain,(
% 3.31/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f43])).
% 3.31/1.03  
% 3.31/1.03  fof(f10,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f29,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f10])).
% 3.31/1.03  
% 3.31/1.03  fof(f66,plain,(
% 3.31/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f29])).
% 3.31/1.03  
% 3.31/1.03  fof(f81,plain,(
% 3.31/1.03    l1_pre_topc(sK1)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f17,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f39,plain,(
% 3.31/1.03    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f17])).
% 3.31/1.03  
% 3.31/1.03  fof(f75,plain,(
% 3.31/1.03    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f39])).
% 3.31/1.03  
% 3.31/1.03  fof(f13,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f33,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f13])).
% 3.31/1.03  
% 3.31/1.03  fof(f46,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(nnf_transformation,[],[f33])).
% 3.31/1.03  
% 3.31/1.03  fof(f69,plain,(
% 3.31/1.03    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f46])).
% 3.31/1.03  
% 3.31/1.03  fof(f87,plain,(
% 3.31/1.03    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f12,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f32,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f12])).
% 3.31/1.03  
% 3.31/1.03  fof(f68,plain,(
% 3.31/1.03    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f32])).
% 3.31/1.03  
% 3.31/1.03  fof(f86,plain,(
% 3.31/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f15,axiom,(
% 3.31/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f36,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.03    inference(ennf_transformation,[],[f15])).
% 3.31/1.03  
% 3.31/1.03  fof(f37,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.03    inference(flattening,[],[f36])).
% 3.31/1.03  
% 3.31/1.03  fof(f73,plain,(
% 3.31/1.03    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f37])).
% 3.31/1.03  
% 3.31/1.03  fof(f84,plain,(
% 3.31/1.03    v1_funct_1(sK3)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f8,axiom,(
% 3.31/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f26,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.31/1.03    inference(ennf_transformation,[],[f8])).
% 3.31/1.03  
% 3.31/1.03  fof(f27,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.31/1.03    inference(flattening,[],[f26])).
% 3.31/1.03  
% 3.31/1.03  fof(f64,plain,(
% 3.31/1.03    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f27])).
% 3.31/1.03  
% 3.31/1.03  fof(f76,plain,(
% 3.31/1.03    ~v2_struct_0(sK0)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f77,plain,(
% 3.31/1.03    v2_pre_topc(sK0)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f78,plain,(
% 3.31/1.03    l1_pre_topc(sK0)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f79,plain,(
% 3.31/1.03    ~v2_struct_0(sK1)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f80,plain,(
% 3.31/1.03    v2_pre_topc(sK1)),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f85,plain,(
% 3.31/1.03    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f9,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f28,plain,(
% 3.31/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f9])).
% 3.31/1.03  
% 3.31/1.03  fof(f65,plain,(
% 3.31/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f28])).
% 3.31/1.03  
% 3.31/1.03  fof(f11,axiom,(
% 3.31/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f30,plain,(
% 3.31/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.31/1.03    inference(ennf_transformation,[],[f11])).
% 3.31/1.03  
% 3.31/1.03  fof(f31,plain,(
% 3.31/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.31/1.03    inference(flattening,[],[f30])).
% 3.31/1.03  
% 3.31/1.03  fof(f67,plain,(
% 3.31/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f31])).
% 3.31/1.03  
% 3.31/1.03  fof(f14,axiom,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f34,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.31/1.03    inference(ennf_transformation,[],[f14])).
% 3.31/1.03  
% 3.31/1.03  fof(f35,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.31/1.03    inference(flattening,[],[f34])).
% 3.31/1.03  
% 3.31/1.03  fof(f47,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.31/1.03    inference(nnf_transformation,[],[f35])).
% 3.31/1.03  
% 3.31/1.03  fof(f72,plain,(
% 3.31/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f47])).
% 3.31/1.03  
% 3.31/1.03  fof(f91,plain,(
% 3.31/1.03    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.31/1.03    inference(equality_resolution,[],[f72])).
% 3.31/1.03  
% 3.31/1.03  fof(f88,plain,(
% 3.31/1.03    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 3.31/1.03    inference(cnf_transformation,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f7,axiom,(
% 3.31/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f20,plain,(
% 3.31/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.31/1.03    inference(pure_predicate_removal,[],[f7])).
% 3.31/1.03  
% 3.31/1.03  fof(f25,plain,(
% 3.31/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/1.03    inference(ennf_transformation,[],[f20])).
% 3.31/1.03  
% 3.31/1.03  fof(f63,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f25])).
% 3.31/1.03  
% 3.31/1.03  fof(f4,axiom,(
% 3.31/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f22,plain,(
% 3.31/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(ennf_transformation,[],[f4])).
% 3.31/1.03  
% 3.31/1.03  fof(f45,plain,(
% 3.31/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(nnf_transformation,[],[f22])).
% 3.31/1.03  
% 3.31/1.03  fof(f59,plain,(
% 3.31/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f45])).
% 3.31/1.03  
% 3.31/1.03  fof(f3,axiom,(
% 3.31/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f21,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f3])).
% 3.31/1.03  
% 3.31/1.03  fof(f58,plain,(
% 3.31/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f21])).
% 3.31/1.03  
% 3.31/1.03  fof(f57,plain,(
% 3.31/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f44])).
% 3.31/1.03  
% 3.31/1.03  fof(f5,axiom,(
% 3.31/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f61,plain,(
% 3.31/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f5])).
% 3.31/1.03  
% 3.31/1.03  fof(f6,axiom,(
% 3.31/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f23,plain,(
% 3.31/1.03    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(ennf_transformation,[],[f6])).
% 3.31/1.03  
% 3.31/1.03  fof(f24,plain,(
% 3.31/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(flattening,[],[f23])).
% 3.31/1.03  
% 3.31/1.03  fof(f62,plain,(
% 3.31/1.03    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f24])).
% 3.31/1.03  
% 3.31/1.03  cnf(c_28,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK2,sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1663,plain,
% 3.31/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_21,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.03      | ~ l1_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1667,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1672,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.31/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3893,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1667,c_1672]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_0,plain,
% 3.31/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.31/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1675,plain,
% 3.31/1.03      ( X0 = X1
% 3.31/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.31/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6133,plain,
% 3.31/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.31/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.31/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_3893,c_1675]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6622,plain,
% 3.31/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.31/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top
% 3.31/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_3893,c_6133]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_13,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_71,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top
% 3.31/1.03      | l1_pre_topc(X0) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3759,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | ~ l1_pre_topc(X1) ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_21,c_4]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3760,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_3759]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8813,plain,
% 3.31/1.03      ( l1_pre_topc(X1) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.03      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_6622,c_71,c_3760,c_6133]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8814,plain,
% 3.31/1.03      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.31/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_8813]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8823,plain,
% 3.31/1.03      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.31/1.03      | m1_pre_topc(sK1,sK2) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1663,c_8814]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_30,negated_conjecture,
% 3.31/1.03      ( l1_pre_topc(sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_41,plain,
% 3.31/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_22,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_48,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X0) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_50,plain,
% 3.31/1.03      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_48]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_17,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ l1_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_63,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_65,plain,
% 3.31/1.03      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.31/1.03      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_63]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2380,plain,
% 3.31/1.03      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_13,c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2381,plain,
% 3.31/1.03      ( l1_pre_topc(sK2) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_24,negated_conjecture,
% 3.31/1.03      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_15,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/1.03      | ~ l1_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1668,plain,
% 3.31/1.03      ( m1_pre_topc(X0,X1) = iProver_top
% 3.31/1.03      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4051,plain,
% 3.31/1.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0,sK2) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_24,c_1668]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4066,plain,
% 3.31/1.03      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.31/1.03      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_4051]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8963,plain,
% 3.31/1.03      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_8823,c_41,c_50,c_65,c_2381,c_4066]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_25,negated_conjecture,
% 3.31/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1665,plain,
% 3.31/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_20,plain,
% 3.31/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.31/1.03      | ~ m1_pre_topc(X3,X1)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_27,negated_conjecture,
% 3.31/1.03      ( v1_funct_1(sK3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_566,plain,
% 3.31/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.31/1.03      | ~ m1_pre_topc(X3,X1)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.31/1.03      | sK3 != X0 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_567,plain,
% 3.31/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | ~ m1_pre_topc(X2,X0)
% 3.31/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v2_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_566]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1652,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2)
% 3.31/1.03      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.31/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 3.31/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0) != iProver_top
% 3.31/1.03      | v2_struct_0(X1) = iProver_top
% 3.31/1.03      | v2_struct_0(X0) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2458,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 3.31/1.03      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK0) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.31/1.03      | v2_struct_0(sK0) = iProver_top
% 3.31/1.03      | v2_struct_0(sK1) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1665,c_1652]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_11,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_602,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.31/1.03      | sK3 != X0 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_603,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.31/1.03      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_602]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1651,plain,
% 3.31/1.03      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 3.31/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2355,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1665,c_1651]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2459,plain,
% 3.31/1.03      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.31/1.03      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK0) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.31/1.03      | v2_struct_0(sK0) = iProver_top
% 3.31/1.03      | v2_struct_0(sK1) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(demodulation,[status(thm)],[c_2458,c_2355]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_35,negated_conjecture,
% 3.31/1.03      ( ~ v2_struct_0(sK0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_36,plain,
% 3.31/1.03      ( v2_struct_0(sK0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_34,negated_conjecture,
% 3.31/1.03      ( v2_pre_topc(sK0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_37,plain,
% 3.31/1.03      ( v2_pre_topc(sK0) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_33,negated_conjecture,
% 3.31/1.03      ( l1_pre_topc(sK0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_38,plain,
% 3.31/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_32,negated_conjecture,
% 3.31/1.03      ( ~ v2_struct_0(sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_39,plain,
% 3.31/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_31,negated_conjecture,
% 3.31/1.03      ( v2_pre_topc(sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_40,plain,
% 3.31/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_26,negated_conjecture,
% 3.31/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_45,plain,
% 3.31/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2595,plain,
% 3.31/1.03      ( k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))
% 3.31/1.03      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_2459,c_36,c_37,c_38,c_39,c_40,c_41,c_45]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2603,plain,
% 3.31/1.03      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1663,c_2595]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_12,plain,
% 3.31/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_14,plain,
% 3.31/1.03      ( v2_struct_0(X0)
% 3.31/1.03      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.31/1.03      | ~ l1_struct_0(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_452,plain,
% 3.31/1.03      ( v2_struct_0(X0)
% 3.31/1.03      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.31/1.03      | ~ l1_pre_topc(X0) ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_12,c_14]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_18,plain,
% 3.31/1.03      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.31/1.03      | ~ v1_funct_2(X4,X2,X3)
% 3.31/1.03      | ~ v1_funct_2(X4,X0,X1)
% 3.31/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.31/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.31/1.03      | v1_xboole_0(X1)
% 3.31/1.03      | v1_xboole_0(X3)
% 3.31/1.03      | ~ v1_funct_1(X4) ),
% 3.31/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_23,negated_conjecture,
% 3.31/1.03      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_491,plain,
% 3.31/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.31/1.03      | ~ v1_funct_2(X0,X3,X4)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.31/1.03      | v1_xboole_0(X4)
% 3.31/1.03      | v1_xboole_0(X2)
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 3.31/1.03      | u1_struct_0(sK2) != X1
% 3.31/1.03      | u1_struct_0(sK0) != X2
% 3.31/1.03      | u1_struct_0(sK0) != X4
% 3.31/1.03      | u1_struct_0(sK1) != X3
% 3.31/1.03      | sK3 != X0 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_492,plain,
% 3.31/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.31/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.31/1.03      | v1_xboole_0(u1_struct_0(sK0))
% 3.31/1.03      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.31/1.03      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_491]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_524,plain,
% 3.31/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.31/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 3.31/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.31/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_452,c_492]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_614,plain,
% 3.31/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.31/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.31/1.03      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_524]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_903,plain,
% 3.31/1.03      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 3.31/1.03      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 3.31/1.03      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.31/1.03      | sP0_iProver_split
% 3.31/1.03      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 3.31/1.03      inference(splitting,
% 3.31/1.03                [splitting(split),new_symbols(definition,[])],
% 3.31/1.03                [c_614]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1649,plain,
% 3.31/1.03      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 3.31/1.03      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | sP0_iProver_split = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2605,plain,
% 3.31/1.03      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | sP0_iProver_split = iProver_top ),
% 3.31/1.03      inference(demodulation,[status(thm)],[c_2603,c_1649]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_902,plain,
% 3.31/1.03      ( v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.31/1.03      | ~ sP0_iProver_split ),
% 3.31/1.03      inference(splitting,
% 3.31/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.31/1.03                [c_614]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_905,plain,( X0 = X0 ),theory(equality) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2173,plain,
% 3.31/1.03      ( v2_struct_0(sK0) | ~ l1_pre_topc(sK0) | ~ sP0_iProver_split ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_902,c_905]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2174,plain,
% 3.31/1.03      ( v2_struct_0(sK0) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.03      | sP0_iProver_split != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2733,plain,
% 3.31/1.03      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_2605,c_36,c_38,c_2174]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2734,plain,
% 3.31/1.03      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_2733]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8972,plain,
% 3.31/1.03      ( k7_relat_1(sK3,u1_struct_0(sK1)) != sK3
% 3.31/1.03      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.31/1.03      inference(demodulation,[status(thm)],[c_8963,c_2734]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_10,plain,
% 3.31/1.03      ( v4_relat_1(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_7,plain,
% 3.31/1.03      ( ~ v4_relat_1(X0,X1)
% 3.31/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 3.31/1.03      | ~ v1_relat_1(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_470,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 3.31/1.03      | ~ v1_relat_1(X0) ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1653,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.31/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2746,plain,
% 3.31/1.03      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 3.31/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1665,c_1653]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_46,plain,
% 3.31/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2175,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2240,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.31/1.03      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_2175]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2241,plain,
% 3.31/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.31/1.03      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_2240]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.31/1.03      | ~ v1_relat_1(X1)
% 3.31/1.03      | v1_relat_1(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_260,plain,
% 3.31/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.31/1.03      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_261,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_260]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_331,plain,
% 3.31/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.31/1.03      inference(bin_hyper_res,[status(thm)],[c_5,c_261]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2024,plain,
% 3.31/1.03      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.31/1.03      | v1_relat_1(X0)
% 3.31/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_331]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2576,plain,
% 3.31/1.03      ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.31/1.03      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.31/1.03      | v1_relat_1(sK3) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_2024]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2577,plain,
% 3.31/1.03      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 3.31/1.03      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 3.31/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_2576]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3020,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3021,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_3020]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3294,plain,
% 3.31/1.03      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_2746,c_46,c_2241,c_2577,c_3021]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9,plain,
% 3.31/1.03      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.31/1.03      | ~ v1_relat_1(X0)
% 3.31/1.03      | k7_relat_1(X0,X1) = X0 ),
% 3.31/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1670,plain,
% 3.31/1.03      ( k7_relat_1(X0,X1) = X0
% 3.31/1.03      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.31/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3876,plain,
% 3.31/1.03      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3
% 3.31/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_3294,c_1670]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4953,plain,
% 3.31/1.03      ( k7_relat_1(sK3,u1_struct_0(sK1)) = sK3 ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_3876,c_46,c_2241,c_2577,c_3021]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8983,plain,
% 3.31/1.03      ( sK3 != sK3
% 3.31/1.03      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.31/1.03      inference(light_normalisation,[status(thm)],[c_8972,c_4953]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8984,plain,
% 3.31/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.31/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.31/1.03      inference(equality_resolution_simp,[status(thm)],[c_8983]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(contradiction,plain,
% 3.31/1.03      ( $false ),
% 3.31/1.03      inference(minisat,[status(thm)],[c_8984,c_46,c_45]) ).
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  ------                               Statistics
% 3.31/1.03  
% 3.31/1.03  ------ Selected
% 3.31/1.03  
% 3.31/1.03  total_time:                             0.328
% 3.31/1.03  
%------------------------------------------------------------------------------
