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
% DateTime   : Thu Dec  3 12:23:17 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  219 (1140 expanded)
%              Number of clauses        :  124 ( 225 expanded)
%              Number of leaves         :   23 ( 449 expanded)
%              Depth                    :   30
%              Number of atoms          : 1743 (20151 expanded)
%              Number of equality atoms :  484 (1657 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal clause size      :   44 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK0(X0,X1,X2))
        & r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK0(X0,X1,X2))
                    & r1_tarski(sK0(X0,X1,X2),X2)
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X1,X4,X5) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | r1_tmap_1(X3,X1,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X5) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X5) )
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X1,X4,X5) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | r1_tmap_1(X3,X1,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X1,X4,X5) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & v1_tsep_1(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                  | ~ r1_tmap_1(X3,X1,sK5,X5) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                  | r1_tmap_1(X3,X1,sK5,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & v1_tsep_1(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X1,X4,X5) )
                      & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & v1_tsep_1(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                      | ~ r1_tmap_1(sK4,X1,X4,X5) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                      | r1_tmap_1(sK4,X1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & v1_tsep_1(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X1,X4,X5) )
                          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                          | ~ r1_tmap_1(X3,X1,X4,X5) )
                        & ( r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                          | r1_tmap_1(X3,X1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & v1_tsep_1(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK2,X4,X5) )
                            & ( r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK2,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      | ~ r1_tmap_1(sK4,sK2,sK5,sK6) )
    & ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      | r1_tmap_1(sK4,sK2,sK5,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK3,sK4)
    & v1_tsep_1(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f49,f56,f55,f54,f53,f52,f51,f50])).

fof(f98,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f57])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f91,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f99,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f93,plain,(
    v1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2923,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2913,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2918,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2921,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3094,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2918,c_2921])).

cnf(c_5311,plain,
    ( m1_connsp_2(u1_struct_0(X0),X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_3094])).

cnf(c_5986,plain,
    ( m1_connsp_2(u1_struct_0(X0),X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X3),X1) != iProver_top
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X3)) != iProver_top
    | r1_tarski(u1_struct_0(X3),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_5311])).

cnf(c_6148,plain,
    ( m1_connsp_2(u1_struct_0(X0),X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_5986])).

cnf(c_23,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK6)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2910,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2988,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2910,c_24])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_891,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_892,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_896,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_31])).

cnf(c_897,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_896])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_944,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_897,c_18])).

cnf(c_2892,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
    | m1_connsp_2(X5,X0,X4) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_3430,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2892])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_50,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2037,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3263,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_3264,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_connsp_2(X4,sK4,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_3270,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3264])).

cnf(c_4213,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3430,c_50,c_3263,c_3270])).

cnf(c_4214,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | m1_connsp_2(X4,sK4,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4213])).

cnf(c_4237,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_connsp_2(X3,sK4,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4214])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_46,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5747,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_connsp_2(X3,sK4,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4237,c_45,c_46,c_47,c_54])).

cnf(c_5748,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_connsp_2(X3,sK4,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5747])).

cnf(c_5766,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | m1_connsp_2(X0,sK4,sK7) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2988,c_5748])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_51,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_56,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_58,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2908,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2951,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2908,c_24])).

cnf(c_21,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_19,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_219,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_220,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_219])).

cnf(c_825,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_220,c_30])).

cnf(c_826,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_830,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_31])).

cnf(c_831,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_830])).

cnf(c_872,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_831,c_18])).

cnf(c_2893,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_3795,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2893])).

cnf(c_3265,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | ~ r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_3266,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3265])).

cnf(c_4187,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3795,c_50])).

cnf(c_4188,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4187])).

cnf(c_4208,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4188])).

cnf(c_5657,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4208,c_45,c_46,c_47,c_54])).

cnf(c_5658,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5657])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2911,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3005,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2911,c_24])).

cnf(c_5673,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5658,c_3005])).

cnf(c_5796,plain,
    ( m1_connsp_2(X0,sK4,sK7) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5766,c_42,c_43,c_44,c_48,c_51,c_56,c_58,c_2951,c_5673])).

cnf(c_5806,plain,
    ( m1_connsp_2(u1_struct_0(X0),sK4,sK7) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_5796])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3274,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3674,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3274])).

cnf(c_3675,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3674])).

cnf(c_5910,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_connsp_2(u1_struct_0(X0),sK4,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5806,c_44,c_51,c_3675])).

cnf(c_5911,plain,
    ( m1_connsp_2(u1_struct_0(X0),sK4,sK7) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5910])).

cnf(c_6160,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | r2_hidden(sK7,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6148,c_5911])).

cnf(c_2905,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2920,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4459,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_2920])).

cnf(c_6208,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6160,c_43,c_44,c_50,c_51,c_3675,c_4459])).

cnf(c_6209,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | r2_hidden(sK7,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6208])).

cnf(c_6218,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_6209])).

cnf(c_2907,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2919,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3897,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_2919])).

cnf(c_16,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_228,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_17])).

cnf(c_229,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_28,negated_conjecture,
    ( v1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_562,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_28])).

cnf(c_563,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_565,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_27])).

cnf(c_2894,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_564,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_3771,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2894,c_44,c_51,c_56,c_564,c_3675])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_521,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_8])).

cnf(c_3436,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_3437,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3436])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3279,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | r2_hidden(sK7,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3280,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6218,c_4459,c_3897,c_3771,c_3675,c_3437,c_3280,c_58,c_56,c_51,c_48,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:16:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.98  
% 2.46/0.98  ------  iProver source info
% 2.46/0.98  
% 2.46/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.98  git: non_committed_changes: false
% 2.46/0.98  git: last_make_outside_of_git: false
% 2.46/0.98  
% 2.46/0.98  ------ 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options
% 2.46/0.98  
% 2.46/0.98  --out_options                           all
% 2.46/0.98  --tptp_safe_out                         true
% 2.46/0.98  --problem_path                          ""
% 2.46/0.98  --include_path                          ""
% 2.46/0.98  --clausifier                            res/vclausify_rel
% 2.46/0.98  --clausifier_options                    --mode clausify
% 2.46/0.98  --stdin                                 false
% 2.46/0.98  --stats_out                             all
% 2.46/0.98  
% 2.46/0.98  ------ General Options
% 2.46/0.98  
% 2.46/0.98  --fof                                   false
% 2.46/0.98  --time_out_real                         305.
% 2.46/0.98  --time_out_virtual                      -1.
% 2.46/0.98  --symbol_type_check                     false
% 2.46/0.98  --clausify_out                          false
% 2.46/0.98  --sig_cnt_out                           false
% 2.46/0.98  --trig_cnt_out                          false
% 2.46/0.98  --trig_cnt_out_tolerance                1.
% 2.46/0.98  --trig_cnt_out_sk_spl                   false
% 2.46/0.98  --abstr_cl_out                          false
% 2.46/0.98  
% 2.46/0.98  ------ Global Options
% 2.46/0.98  
% 2.46/0.98  --schedule                              default
% 2.46/0.98  --add_important_lit                     false
% 2.46/0.98  --prop_solver_per_cl                    1000
% 2.46/0.98  --min_unsat_core                        false
% 2.46/0.98  --soft_assumptions                      false
% 2.46/0.98  --soft_lemma_size                       3
% 2.46/0.98  --prop_impl_unit_size                   0
% 2.46/0.98  --prop_impl_unit                        []
% 2.46/0.98  --share_sel_clauses                     true
% 2.46/0.98  --reset_solvers                         false
% 2.46/0.98  --bc_imp_inh                            [conj_cone]
% 2.46/0.98  --conj_cone_tolerance                   3.
% 2.46/0.98  --extra_neg_conj                        none
% 2.46/0.98  --large_theory_mode                     true
% 2.46/0.98  --prolific_symb_bound                   200
% 2.46/0.98  --lt_threshold                          2000
% 2.46/0.98  --clause_weak_htbl                      true
% 2.46/0.98  --gc_record_bc_elim                     false
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing Options
% 2.46/0.98  
% 2.46/0.98  --preprocessing_flag                    true
% 2.46/0.98  --time_out_prep_mult                    0.1
% 2.46/0.98  --splitting_mode                        input
% 2.46/0.98  --splitting_grd                         true
% 2.46/0.98  --splitting_cvd                         false
% 2.46/0.98  --splitting_cvd_svl                     false
% 2.46/0.98  --splitting_nvd                         32
% 2.46/0.98  --sub_typing                            true
% 2.46/0.98  --prep_gs_sim                           true
% 2.46/0.98  --prep_unflatten                        true
% 2.46/0.98  --prep_res_sim                          true
% 2.46/0.98  --prep_upred                            true
% 2.46/0.98  --prep_sem_filter                       exhaustive
% 2.46/0.98  --prep_sem_filter_out                   false
% 2.46/0.98  --pred_elim                             true
% 2.46/0.98  --res_sim_input                         true
% 2.46/0.98  --eq_ax_congr_red                       true
% 2.46/0.98  --pure_diseq_elim                       true
% 2.46/0.98  --brand_transform                       false
% 2.46/0.98  --non_eq_to_eq                          false
% 2.46/0.98  --prep_def_merge                        true
% 2.46/0.98  --prep_def_merge_prop_impl              false
% 2.46/0.98  --prep_def_merge_mbd                    true
% 2.46/0.98  --prep_def_merge_tr_red                 false
% 2.46/0.98  --prep_def_merge_tr_cl                  false
% 2.46/0.98  --smt_preprocessing                     true
% 2.46/0.98  --smt_ac_axioms                         fast
% 2.46/0.98  --preprocessed_out                      false
% 2.46/0.98  --preprocessed_stats                    false
% 2.46/0.98  
% 2.46/0.98  ------ Abstraction refinement Options
% 2.46/0.98  
% 2.46/0.98  --abstr_ref                             []
% 2.46/0.98  --abstr_ref_prep                        false
% 2.46/0.98  --abstr_ref_until_sat                   false
% 2.46/0.98  --abstr_ref_sig_restrict                funpre
% 2.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.98  --abstr_ref_under                       []
% 2.46/0.98  
% 2.46/0.98  ------ SAT Options
% 2.46/0.98  
% 2.46/0.98  --sat_mode                              false
% 2.46/0.98  --sat_fm_restart_options                ""
% 2.46/0.98  --sat_gr_def                            false
% 2.46/0.98  --sat_epr_types                         true
% 2.46/0.98  --sat_non_cyclic_types                  false
% 2.46/0.98  --sat_finite_models                     false
% 2.46/0.98  --sat_fm_lemmas                         false
% 2.46/0.98  --sat_fm_prep                           false
% 2.46/0.98  --sat_fm_uc_incr                        true
% 2.46/0.98  --sat_out_model                         small
% 2.46/0.98  --sat_out_clauses                       false
% 2.46/0.98  
% 2.46/0.98  ------ QBF Options
% 2.46/0.98  
% 2.46/0.98  --qbf_mode                              false
% 2.46/0.98  --qbf_elim_univ                         false
% 2.46/0.98  --qbf_dom_inst                          none
% 2.46/0.98  --qbf_dom_pre_inst                      false
% 2.46/0.98  --qbf_sk_in                             false
% 2.46/0.98  --qbf_pred_elim                         true
% 2.46/0.98  --qbf_split                             512
% 2.46/0.98  
% 2.46/0.98  ------ BMC1 Options
% 2.46/0.98  
% 2.46/0.98  --bmc1_incremental                      false
% 2.46/0.98  --bmc1_axioms                           reachable_all
% 2.46/0.98  --bmc1_min_bound                        0
% 2.46/0.98  --bmc1_max_bound                        -1
% 2.46/0.98  --bmc1_max_bound_default                -1
% 2.46/0.98  --bmc1_symbol_reachability              true
% 2.46/0.98  --bmc1_property_lemmas                  false
% 2.46/0.98  --bmc1_k_induction                      false
% 2.46/0.98  --bmc1_non_equiv_states                 false
% 2.46/0.98  --bmc1_deadlock                         false
% 2.46/0.98  --bmc1_ucm                              false
% 2.46/0.98  --bmc1_add_unsat_core                   none
% 2.46/0.98  --bmc1_unsat_core_children              false
% 2.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.98  --bmc1_out_stat                         full
% 2.46/0.98  --bmc1_ground_init                      false
% 2.46/0.98  --bmc1_pre_inst_next_state              false
% 2.46/0.98  --bmc1_pre_inst_state                   false
% 2.46/0.98  --bmc1_pre_inst_reach_state             false
% 2.46/0.98  --bmc1_out_unsat_core                   false
% 2.46/0.98  --bmc1_aig_witness_out                  false
% 2.46/0.98  --bmc1_verbose                          false
% 2.46/0.98  --bmc1_dump_clauses_tptp                false
% 2.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.98  --bmc1_dump_file                        -
% 2.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.98  --bmc1_ucm_extend_mode                  1
% 2.46/0.98  --bmc1_ucm_init_mode                    2
% 2.46/0.98  --bmc1_ucm_cone_mode                    none
% 2.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.98  --bmc1_ucm_relax_model                  4
% 2.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.98  --bmc1_ucm_layered_model                none
% 2.46/0.98  --bmc1_ucm_max_lemma_size               10
% 2.46/0.98  
% 2.46/0.98  ------ AIG Options
% 2.46/0.98  
% 2.46/0.98  --aig_mode                              false
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation Options
% 2.46/0.98  
% 2.46/0.98  --instantiation_flag                    true
% 2.46/0.98  --inst_sos_flag                         false
% 2.46/0.98  --inst_sos_phase                        true
% 2.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel_side                     num_symb
% 2.46/0.98  --inst_solver_per_active                1400
% 2.46/0.98  --inst_solver_calls_frac                1.
% 2.46/0.98  --inst_passive_queue_type               priority_queues
% 2.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.98  --inst_passive_queues_freq              [25;2]
% 2.46/0.98  --inst_dismatching                      true
% 2.46/0.98  --inst_eager_unprocessed_to_passive     true
% 2.46/0.98  --inst_prop_sim_given                   true
% 2.46/0.98  --inst_prop_sim_new                     false
% 2.46/0.98  --inst_subs_new                         false
% 2.46/0.98  --inst_eq_res_simp                      false
% 2.46/0.98  --inst_subs_given                       false
% 2.46/0.98  --inst_orphan_elimination               true
% 2.46/0.98  --inst_learning_loop_flag               true
% 2.46/0.98  --inst_learning_start                   3000
% 2.46/0.98  --inst_learning_factor                  2
% 2.46/0.98  --inst_start_prop_sim_after_learn       3
% 2.46/0.98  --inst_sel_renew                        solver
% 2.46/0.98  --inst_lit_activity_flag                true
% 2.46/0.98  --inst_restr_to_given                   false
% 2.46/0.98  --inst_activity_threshold               500
% 2.46/0.98  --inst_out_proof                        true
% 2.46/0.98  
% 2.46/0.98  ------ Resolution Options
% 2.46/0.98  
% 2.46/0.98  --resolution_flag                       true
% 2.46/0.98  --res_lit_sel                           adaptive
% 2.46/0.98  --res_lit_sel_side                      none
% 2.46/0.98  --res_ordering                          kbo
% 2.46/0.98  --res_to_prop_solver                    active
% 2.46/0.98  --res_prop_simpl_new                    false
% 2.46/0.98  --res_prop_simpl_given                  true
% 2.46/0.98  --res_passive_queue_type                priority_queues
% 2.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.98  --res_passive_queues_freq               [15;5]
% 2.46/0.98  --res_forward_subs                      full
% 2.46/0.98  --res_backward_subs                     full
% 2.46/0.98  --res_forward_subs_resolution           true
% 2.46/0.98  --res_backward_subs_resolution          true
% 2.46/0.98  --res_orphan_elimination                true
% 2.46/0.98  --res_time_limit                        2.
% 2.46/0.98  --res_out_proof                         true
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Options
% 2.46/0.98  
% 2.46/0.98  --superposition_flag                    true
% 2.46/0.98  --sup_passive_queue_type                priority_queues
% 2.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.98  --demod_completeness_check              fast
% 2.46/0.98  --demod_use_ground                      true
% 2.46/0.98  --sup_to_prop_solver                    passive
% 2.46/0.98  --sup_prop_simpl_new                    true
% 2.46/0.98  --sup_prop_simpl_given                  true
% 2.46/0.98  --sup_fun_splitting                     false
% 2.46/0.98  --sup_smt_interval                      50000
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Simplification Setup
% 2.46/0.98  
% 2.46/0.98  --sup_indices_passive                   []
% 2.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_full_bw                           [BwDemod]
% 2.46/0.98  --sup_immed_triv                        [TrivRules]
% 2.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_immed_bw_main                     []
% 2.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  
% 2.46/0.98  ------ Combination Options
% 2.46/0.98  
% 2.46/0.98  --comb_res_mult                         3
% 2.46/0.98  --comb_sup_mult                         2
% 2.46/0.98  --comb_inst_mult                        10
% 2.46/0.98  
% 2.46/0.98  ------ Debug Options
% 2.46/0.98  
% 2.46/0.98  --dbg_backtrace                         false
% 2.46/0.98  --dbg_dump_prop_clauses                 false
% 2.46/0.98  --dbg_dump_prop_clauses_file            -
% 2.46/0.98  --dbg_out_stat                          false
% 2.46/0.98  ------ Parsing...
% 2.46/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/0.98  ------ Proving...
% 2.46/0.98  ------ Problem Properties 
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  clauses                                 34
% 2.46/0.98  conjectures                             17
% 2.46/0.98  EPR                                     18
% 2.46/0.98  Horn                                    25
% 2.46/0.98  unary                                   16
% 2.46/0.98  binary                                  2
% 2.46/0.98  lits                                    125
% 2.46/0.98  lits eq                                 6
% 2.46/0.98  fd_pure                                 0
% 2.46/0.98  fd_pseudo                               0
% 2.46/0.98  fd_cond                                 0
% 2.46/0.98  fd_pseudo_cond                          1
% 2.46/0.98  AC symbols                              0
% 2.46/0.98  
% 2.46/0.98  ------ Schedule dynamic 5 is on 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  ------ 
% 2.46/0.98  Current options:
% 2.46/0.98  ------ 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options
% 2.46/0.98  
% 2.46/0.98  --out_options                           all
% 2.46/0.98  --tptp_safe_out                         true
% 2.46/0.98  --problem_path                          ""
% 2.46/0.98  --include_path                          ""
% 2.46/0.98  --clausifier                            res/vclausify_rel
% 2.46/0.98  --clausifier_options                    --mode clausify
% 2.46/0.98  --stdin                                 false
% 2.46/0.98  --stats_out                             all
% 2.46/0.98  
% 2.46/0.98  ------ General Options
% 2.46/0.98  
% 2.46/0.98  --fof                                   false
% 2.46/0.98  --time_out_real                         305.
% 2.46/0.98  --time_out_virtual                      -1.
% 2.46/0.98  --symbol_type_check                     false
% 2.46/0.98  --clausify_out                          false
% 2.46/0.98  --sig_cnt_out                           false
% 2.46/0.98  --trig_cnt_out                          false
% 2.46/0.98  --trig_cnt_out_tolerance                1.
% 2.46/0.98  --trig_cnt_out_sk_spl                   false
% 2.46/0.98  --abstr_cl_out                          false
% 2.46/0.98  
% 2.46/0.98  ------ Global Options
% 2.46/0.98  
% 2.46/0.98  --schedule                              default
% 2.46/0.98  --add_important_lit                     false
% 2.46/0.98  --prop_solver_per_cl                    1000
% 2.46/0.98  --min_unsat_core                        false
% 2.46/0.98  --soft_assumptions                      false
% 2.46/0.98  --soft_lemma_size                       3
% 2.46/0.98  --prop_impl_unit_size                   0
% 2.46/0.98  --prop_impl_unit                        []
% 2.46/0.98  --share_sel_clauses                     true
% 2.46/0.98  --reset_solvers                         false
% 2.46/0.98  --bc_imp_inh                            [conj_cone]
% 2.46/0.98  --conj_cone_tolerance                   3.
% 2.46/0.98  --extra_neg_conj                        none
% 2.46/0.98  --large_theory_mode                     true
% 2.46/0.98  --prolific_symb_bound                   200
% 2.46/0.98  --lt_threshold                          2000
% 2.46/0.98  --clause_weak_htbl                      true
% 2.46/0.98  --gc_record_bc_elim                     false
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing Options
% 2.46/0.98  
% 2.46/0.98  --preprocessing_flag                    true
% 2.46/0.98  --time_out_prep_mult                    0.1
% 2.46/0.98  --splitting_mode                        input
% 2.46/0.98  --splitting_grd                         true
% 2.46/0.98  --splitting_cvd                         false
% 2.46/0.98  --splitting_cvd_svl                     false
% 2.46/0.98  --splitting_nvd                         32
% 2.46/0.98  --sub_typing                            true
% 2.46/0.98  --prep_gs_sim                           true
% 2.46/0.98  --prep_unflatten                        true
% 2.46/0.98  --prep_res_sim                          true
% 2.46/0.98  --prep_upred                            true
% 2.46/0.98  --prep_sem_filter                       exhaustive
% 2.46/0.98  --prep_sem_filter_out                   false
% 2.46/0.98  --pred_elim                             true
% 2.46/0.98  --res_sim_input                         true
% 2.46/0.98  --eq_ax_congr_red                       true
% 2.46/0.98  --pure_diseq_elim                       true
% 2.46/0.98  --brand_transform                       false
% 2.46/0.98  --non_eq_to_eq                          false
% 2.46/0.98  --prep_def_merge                        true
% 2.46/0.98  --prep_def_merge_prop_impl              false
% 2.46/0.98  --prep_def_merge_mbd                    true
% 2.46/0.98  --prep_def_merge_tr_red                 false
% 2.46/0.98  --prep_def_merge_tr_cl                  false
% 2.46/0.98  --smt_preprocessing                     true
% 2.46/0.98  --smt_ac_axioms                         fast
% 2.46/0.98  --preprocessed_out                      false
% 2.46/0.98  --preprocessed_stats                    false
% 2.46/0.98  
% 2.46/0.98  ------ Abstraction refinement Options
% 2.46/0.98  
% 2.46/0.98  --abstr_ref                             []
% 2.46/0.98  --abstr_ref_prep                        false
% 2.46/0.98  --abstr_ref_until_sat                   false
% 2.46/0.98  --abstr_ref_sig_restrict                funpre
% 2.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.98  --abstr_ref_under                       []
% 2.46/0.98  
% 2.46/0.98  ------ SAT Options
% 2.46/0.98  
% 2.46/0.98  --sat_mode                              false
% 2.46/0.98  --sat_fm_restart_options                ""
% 2.46/0.98  --sat_gr_def                            false
% 2.46/0.98  --sat_epr_types                         true
% 2.46/0.98  --sat_non_cyclic_types                  false
% 2.46/0.98  --sat_finite_models                     false
% 2.46/0.98  --sat_fm_lemmas                         false
% 2.46/0.98  --sat_fm_prep                           false
% 2.46/0.98  --sat_fm_uc_incr                        true
% 2.46/0.98  --sat_out_model                         small
% 2.46/0.98  --sat_out_clauses                       false
% 2.46/0.98  
% 2.46/0.98  ------ QBF Options
% 2.46/0.98  
% 2.46/0.98  --qbf_mode                              false
% 2.46/0.98  --qbf_elim_univ                         false
% 2.46/0.98  --qbf_dom_inst                          none
% 2.46/0.98  --qbf_dom_pre_inst                      false
% 2.46/0.98  --qbf_sk_in                             false
% 2.46/0.98  --qbf_pred_elim                         true
% 2.46/0.98  --qbf_split                             512
% 2.46/0.98  
% 2.46/0.98  ------ BMC1 Options
% 2.46/0.98  
% 2.46/0.98  --bmc1_incremental                      false
% 2.46/0.98  --bmc1_axioms                           reachable_all
% 2.46/0.98  --bmc1_min_bound                        0
% 2.46/0.98  --bmc1_max_bound                        -1
% 2.46/0.98  --bmc1_max_bound_default                -1
% 2.46/0.98  --bmc1_symbol_reachability              true
% 2.46/0.98  --bmc1_property_lemmas                  false
% 2.46/0.98  --bmc1_k_induction                      false
% 2.46/0.98  --bmc1_non_equiv_states                 false
% 2.46/0.98  --bmc1_deadlock                         false
% 2.46/0.98  --bmc1_ucm                              false
% 2.46/0.98  --bmc1_add_unsat_core                   none
% 2.46/0.98  --bmc1_unsat_core_children              false
% 2.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.98  --bmc1_out_stat                         full
% 2.46/0.98  --bmc1_ground_init                      false
% 2.46/0.98  --bmc1_pre_inst_next_state              false
% 2.46/0.98  --bmc1_pre_inst_state                   false
% 2.46/0.98  --bmc1_pre_inst_reach_state             false
% 2.46/0.98  --bmc1_out_unsat_core                   false
% 2.46/0.98  --bmc1_aig_witness_out                  false
% 2.46/0.98  --bmc1_verbose                          false
% 2.46/0.98  --bmc1_dump_clauses_tptp                false
% 2.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.98  --bmc1_dump_file                        -
% 2.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.98  --bmc1_ucm_extend_mode                  1
% 2.46/0.98  --bmc1_ucm_init_mode                    2
% 2.46/0.98  --bmc1_ucm_cone_mode                    none
% 2.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.98  --bmc1_ucm_relax_model                  4
% 2.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.98  --bmc1_ucm_layered_model                none
% 2.46/0.98  --bmc1_ucm_max_lemma_size               10
% 2.46/0.98  
% 2.46/0.98  ------ AIG Options
% 2.46/0.98  
% 2.46/0.98  --aig_mode                              false
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation Options
% 2.46/0.98  
% 2.46/0.98  --instantiation_flag                    true
% 2.46/0.98  --inst_sos_flag                         false
% 2.46/0.98  --inst_sos_phase                        true
% 2.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel_side                     none
% 2.46/0.98  --inst_solver_per_active                1400
% 2.46/0.98  --inst_solver_calls_frac                1.
% 2.46/0.98  --inst_passive_queue_type               priority_queues
% 2.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.98  --inst_passive_queues_freq              [25;2]
% 2.46/0.98  --inst_dismatching                      true
% 2.46/0.98  --inst_eager_unprocessed_to_passive     true
% 2.46/0.98  --inst_prop_sim_given                   true
% 2.46/0.98  --inst_prop_sim_new                     false
% 2.46/0.98  --inst_subs_new                         false
% 2.46/0.98  --inst_eq_res_simp                      false
% 2.46/0.98  --inst_subs_given                       false
% 2.46/0.98  --inst_orphan_elimination               true
% 2.46/0.98  --inst_learning_loop_flag               true
% 2.46/0.98  --inst_learning_start                   3000
% 2.46/0.98  --inst_learning_factor                  2
% 2.46/0.98  --inst_start_prop_sim_after_learn       3
% 2.46/0.98  --inst_sel_renew                        solver
% 2.46/0.98  --inst_lit_activity_flag                true
% 2.46/0.98  --inst_restr_to_given                   false
% 2.46/0.98  --inst_activity_threshold               500
% 2.46/0.98  --inst_out_proof                        true
% 2.46/0.98  
% 2.46/0.98  ------ Resolution Options
% 2.46/0.98  
% 2.46/0.98  --resolution_flag                       false
% 2.46/0.98  --res_lit_sel                           adaptive
% 2.46/0.98  --res_lit_sel_side                      none
% 2.46/0.98  --res_ordering                          kbo
% 2.46/0.98  --res_to_prop_solver                    active
% 2.46/0.98  --res_prop_simpl_new                    false
% 2.46/0.98  --res_prop_simpl_given                  true
% 2.46/0.98  --res_passive_queue_type                priority_queues
% 2.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.98  --res_passive_queues_freq               [15;5]
% 2.46/0.98  --res_forward_subs                      full
% 2.46/0.98  --res_backward_subs                     full
% 2.46/0.98  --res_forward_subs_resolution           true
% 2.46/0.98  --res_backward_subs_resolution          true
% 2.46/0.98  --res_orphan_elimination                true
% 2.46/0.98  --res_time_limit                        2.
% 2.46/0.98  --res_out_proof                         true
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Options
% 2.46/0.98  
% 2.46/0.98  --superposition_flag                    true
% 2.46/0.98  --sup_passive_queue_type                priority_queues
% 2.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.98  --demod_completeness_check              fast
% 2.46/0.98  --demod_use_ground                      true
% 2.46/0.98  --sup_to_prop_solver                    passive
% 2.46/0.98  --sup_prop_simpl_new                    true
% 2.46/0.98  --sup_prop_simpl_given                  true
% 2.46/0.98  --sup_fun_splitting                     false
% 2.46/0.98  --sup_smt_interval                      50000
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Simplification Setup
% 2.46/0.98  
% 2.46/0.98  --sup_indices_passive                   []
% 2.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_full_bw                           [BwDemod]
% 2.46/0.98  --sup_immed_triv                        [TrivRules]
% 2.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_immed_bw_main                     []
% 2.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  
% 2.46/0.98  ------ Combination Options
% 2.46/0.98  
% 2.46/0.98  --comb_res_mult                         3
% 2.46/0.98  --comb_sup_mult                         2
% 2.46/0.98  --comb_inst_mult                        10
% 2.46/0.98  
% 2.46/0.98  ------ Debug Options
% 2.46/0.98  
% 2.46/0.98  --dbg_backtrace                         false
% 2.46/0.98  --dbg_dump_prop_clauses                 false
% 2.46/0.98  --dbg_dump_prop_clauses_file            -
% 2.46/0.98  --dbg_out_stat                          false
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  ------ Proving...
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  % SZS status Theorem for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  fof(f1,axiom,(
% 2.46/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f39,plain,(
% 2.46/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/0.98    inference(nnf_transformation,[],[f1])).
% 2.46/0.98  
% 2.46/0.98  fof(f40,plain,(
% 2.46/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/0.98    inference(flattening,[],[f39])).
% 2.46/0.98  
% 2.46/0.98  fof(f59,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.46/0.98    inference(cnf_transformation,[],[f40])).
% 2.46/0.98  
% 2.46/0.98  fof(f100,plain,(
% 2.46/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.46/0.98    inference(equality_resolution,[],[f59])).
% 2.46/0.98  
% 2.46/0.98  fof(f10,axiom,(
% 2.46/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f30,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f10])).
% 2.46/0.98  
% 2.46/0.98  fof(f75,plain,(
% 2.46/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f30])).
% 2.46/0.98  
% 2.46/0.98  fof(f8,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f26,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f8])).
% 2.46/0.98  
% 2.46/0.98  fof(f27,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f26])).
% 2.46/0.98  
% 2.46/0.98  fof(f41,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f27])).
% 2.46/0.98  
% 2.46/0.98  fof(f42,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(rectify,[],[f41])).
% 2.46/0.98  
% 2.46/0.98  fof(f43,plain,(
% 2.46/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f44,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.46/0.98  
% 2.46/0.98  fof(f71,plain,(
% 2.46/0.98    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f44])).
% 2.46/0.98  
% 2.46/0.98  fof(f3,axiom,(
% 2.46/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f18,plain,(
% 2.46/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.46/0.98    inference(ennf_transformation,[],[f3])).
% 2.46/0.98  
% 2.46/0.98  fof(f19,plain,(
% 2.46/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.46/0.98    inference(flattening,[],[f18])).
% 2.46/0.98  
% 2.46/0.98  fof(f62,plain,(
% 2.46/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f19])).
% 2.46/0.98  
% 2.46/0.98  fof(f14,conjecture,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f15,negated_conjecture,(
% 2.46/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.46/0.98    inference(negated_conjecture,[],[f14])).
% 2.46/0.98  
% 2.46/0.98  fof(f37,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f15])).
% 2.46/0.98  
% 2.46/0.98  fof(f38,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f37])).
% 2.46/0.98  
% 2.46/0.98  fof(f48,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f38])).
% 2.46/0.98  
% 2.46/0.98  fof(f49,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f48])).
% 2.46/0.98  
% 2.46/0.98  fof(f56,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f55,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f54,plain,(
% 2.46/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X1,sK5,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) | r1_tmap_1(X3,X1,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f53,plain,(
% 2.46/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) | r1_tmap_1(sK4,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f52,plain,(
% 2.46/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & v1_tsep_1(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f51,plain,(
% 2.46/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f50,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f57,plain,(
% 2.46/0.98    (((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK2,sK5,sK6)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK2,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & v1_tsep_1(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f49,f56,f55,f54,f53,f52,f51,f50])).
% 2.46/0.98  
% 2.46/0.98  fof(f98,plain,(
% 2.46/0.98    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f97,plain,(
% 2.46/0.98    sK6 = sK7),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f13,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f35,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f13])).
% 2.46/0.98  
% 2.46/0.98  fof(f36,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f35])).
% 2.46/0.98  
% 2.46/0.98  fof(f47,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f36])).
% 2.46/0.98  
% 2.46/0.98  fof(f79,plain,(
% 2.46/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f47])).
% 2.46/0.98  
% 2.46/0.98  fof(f106,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(equality_resolution,[],[f79])).
% 2.46/0.98  
% 2.46/0.98  fof(f91,plain,(
% 2.46/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f90,plain,(
% 2.46/0.98    v1_funct_1(sK5)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f11,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f31,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f11])).
% 2.46/0.98  
% 2.46/0.98  fof(f32,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.46/0.98    inference(flattening,[],[f31])).
% 2.46/0.98  
% 2.46/0.98  fof(f76,plain,(
% 2.46/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f32])).
% 2.46/0.98  
% 2.46/0.98  fof(f88,plain,(
% 2.46/0.98    ~v2_struct_0(sK4)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f83,plain,(
% 2.46/0.98    ~v2_struct_0(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f84,plain,(
% 2.46/0.98    v2_pre_topc(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f85,plain,(
% 2.46/0.98    l1_pre_topc(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f92,plain,(
% 2.46/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f80,plain,(
% 2.46/0.98    ~v2_struct_0(sK1)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f81,plain,(
% 2.46/0.98    v2_pre_topc(sK1)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f82,plain,(
% 2.46/0.98    l1_pre_topc(sK1)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f86,plain,(
% 2.46/0.98    ~v2_struct_0(sK3)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f89,plain,(
% 2.46/0.98    m1_pre_topc(sK4,sK1)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f94,plain,(
% 2.46/0.98    m1_pre_topc(sK3,sK4)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f96,plain,(
% 2.46/0.98    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f95,plain,(
% 2.46/0.98    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f78,plain,(
% 2.46/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f47])).
% 2.46/0.98  
% 2.46/0.98  fof(f107,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(equality_resolution,[],[f78])).
% 2.46/0.98  
% 2.46/0.98  fof(f12,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f33,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f12])).
% 2.46/0.98  
% 2.46/0.98  fof(f34,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f33])).
% 2.46/0.98  
% 2.46/0.98  fof(f77,plain,(
% 2.46/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f34])).
% 2.46/0.98  
% 2.46/0.98  fof(f105,plain,(
% 2.46/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(equality_resolution,[],[f77])).
% 2.46/0.98  
% 2.46/0.98  fof(f99,plain,(
% 2.46/0.98    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f6,axiom,(
% 2.46/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f23,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f6])).
% 2.46/0.98  
% 2.46/0.98  fof(f65,plain,(
% 2.46/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f23])).
% 2.46/0.98  
% 2.46/0.98  fof(f4,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f20,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f4])).
% 2.46/0.98  
% 2.46/0.98  fof(f21,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.46/0.98    inference(flattening,[],[f20])).
% 2.46/0.98  
% 2.46/0.98  fof(f63,plain,(
% 2.46/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f21])).
% 2.46/0.98  
% 2.46/0.98  fof(f9,axiom,(
% 2.46/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f28,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f9])).
% 2.46/0.98  
% 2.46/0.98  fof(f29,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.46/0.98    inference(flattening,[],[f28])).
% 2.46/0.98  
% 2.46/0.98  fof(f45,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f29])).
% 2.46/0.98  
% 2.46/0.98  fof(f46,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.46/0.98    inference(flattening,[],[f45])).
% 2.46/0.98  
% 2.46/0.98  fof(f72,plain,(
% 2.46/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f46])).
% 2.46/0.98  
% 2.46/0.98  fof(f104,plain,(
% 2.46/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.46/0.98    inference(equality_resolution,[],[f72])).
% 2.46/0.98  
% 2.46/0.98  fof(f93,plain,(
% 2.46/0.98    v1_tsep_1(sK3,sK4)),
% 2.46/0.98    inference(cnf_transformation,[],[f57])).
% 2.46/0.98  
% 2.46/0.98  fof(f5,axiom,(
% 2.46/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f22,plain,(
% 2.46/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f5])).
% 2.46/0.98  
% 2.46/0.98  fof(f64,plain,(
% 2.46/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f22])).
% 2.46/0.98  
% 2.46/0.98  fof(f7,axiom,(
% 2.46/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f24,plain,(
% 2.46/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f7])).
% 2.46/0.98  
% 2.46/0.98  fof(f25,plain,(
% 2.46/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.46/0.98    inference(flattening,[],[f24])).
% 2.46/0.98  
% 2.46/0.98  fof(f66,plain,(
% 2.46/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f25])).
% 2.46/0.98  
% 2.46/0.98  fof(f2,axiom,(
% 2.46/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f16,plain,(
% 2.46/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.46/0.98    inference(ennf_transformation,[],[f2])).
% 2.46/0.98  
% 2.46/0.98  fof(f17,plain,(
% 2.46/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.46/0.98    inference(flattening,[],[f16])).
% 2.46/0.98  
% 2.46/0.98  fof(f61,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f17])).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1,plain,
% 2.46/0.98      ( r1_tarski(X0,X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2923,plain,
% 2.46/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_17,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | ~ l1_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2913,plain,
% 2.46/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_9,plain,
% 2.46/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.46/0.98      | ~ v3_pre_topc(X3,X1)
% 2.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.46/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | ~ r2_hidden(X2,X3)
% 2.46/0.98      | ~ r1_tarski(X3,X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2918,plain,
% 2.46/0.98      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 2.46/0.98      | v3_pre_topc(X3,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.46/0.98      | r2_hidden(X2,X3) != iProver_top
% 2.46/0.98      | r1_tarski(X3,X0) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4,plain,
% 2.46/0.98      ( m1_subset_1(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.46/0.98      | ~ r2_hidden(X0,X2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2921,plain,
% 2.46/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.46/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.46/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3094,plain,
% 2.46/0.98      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 2.46/0.98      | v3_pre_topc(X3,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.46/0.98      | r2_hidden(X2,X3) != iProver_top
% 2.46/0.98      | r1_tarski(X3,X0) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(forward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_2918,c_2921]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5311,plain,
% 2.46/0.98      ( m1_connsp_2(u1_struct_0(X0),X1,X2) = iProver_top
% 2.46/0.98      | v3_pre_topc(X3,X1) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.46/0.98      | r2_hidden(X2,X3) != iProver_top
% 2.46/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2913,c_3094]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5986,plain,
% 2.46/0.98      ( m1_connsp_2(u1_struct_0(X0),X1,X2) = iProver_top
% 2.46/0.98      | v3_pre_topc(u1_struct_0(X3),X1) != iProver_top
% 2.46/0.98      | m1_pre_topc(X3,X1) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 2.46/0.98      | r2_hidden(X2,u1_struct_0(X3)) != iProver_top
% 2.46/0.98      | r1_tarski(u1_struct_0(X3),u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2913,c_5311]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6148,plain,
% 2.46/0.98      ( m1_connsp_2(u1_struct_0(X0),X1,X2) = iProver_top
% 2.46/0.98      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 2.46/0.98      | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2923,c_5986]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_23,negated_conjecture,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.46/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.46/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2910,plain,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_24,negated_conjecture,
% 2.46/0.98      ( sK6 = sK7 ),
% 2.46/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2988,plain,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.46/0.98      inference(light_normalisation,[status(thm)],[c_2910,c_24]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_20,plain,
% 2.46/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.46/0.98      | ~ m1_connsp_2(X6,X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.46/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f106]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_30,negated_conjecture,
% 2.46/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.46/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_891,plain,
% 2.46/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ m1_connsp_2(X6,X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.46/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5)
% 2.46/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.46/0.98      | sK5 != X2 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_892,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ m1_connsp_2(X5,X3,X4)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,X2)
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.46/0.98      | ~ v1_funct_1(sK5)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_891]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_31,negated_conjecture,
% 2.46/0.98      ( v1_funct_1(sK5) ),
% 2.46/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_896,plain,
% 2.46/0.98      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_pre_topc(X0,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_connsp_2(X5,X3,X4)
% 2.46/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_892,c_31]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_897,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ m1_connsp_2(X5,X3,X4)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,X2)
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_896]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_18,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | ~ m1_pre_topc(X2,X0)
% 2.46/0.98      | m1_pre_topc(X2,X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_944,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ m1_connsp_2(X5,X3,X4)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(forward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_897,c_18]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2892,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.46/0.98      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
% 2.46/0.98      | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
% 2.46/0.98      | m1_connsp_2(X5,X0,X4) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.46/0.98      | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X3) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(X3) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X3) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3430,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.46/0.98      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(equality_resolution,[status(thm)],[c_2892]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_33,negated_conjecture,
% 2.46/0.98      ( ~ v2_struct_0(sK4) ),
% 2.46/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_50,plain,
% 2.46/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2037,plain,( X0 = X0 ),theory(equality) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3263,plain,
% 2.46/0.98      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_2037]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3264,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.46/0.98      | r1_tmap_1(sK4,X1,sK5,X3)
% 2.46/0.98      | ~ m1_connsp_2(X4,sK4,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.46/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.46/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.46/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(sK4)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.46/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_944]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3270,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.46/0.98      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_3264]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4213,plain,
% 2.46/0.98      ( v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.46/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_3430,c_50,c_3263,c_3270]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4214,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.46/0.98      | m1_connsp_2(X4,sK4,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_4213]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4237,plain,
% 2.46/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.46/0.98      | m1_connsp_2(X3,sK4,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.46/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(sK2) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.46/0.98      inference(equality_resolution,[status(thm)],[c_4214]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_38,negated_conjecture,
% 2.46/0.98      ( ~ v2_struct_0(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_45,plain,
% 2.46/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_37,negated_conjecture,
% 2.46/0.98      ( v2_pre_topc(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_46,plain,
% 2.46/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_36,negated_conjecture,
% 2.46/0.98      ( l1_pre_topc(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_47,plain,
% 2.46/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_29,negated_conjecture,
% 2.46/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.46/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_54,plain,
% 2.46/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5747,plain,
% 2.46/0.98      ( v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.46/0.98      | m1_connsp_2(X3,sK4,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_4237,c_45,c_46,c_47,c_54]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5748,plain,
% 2.46/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.46/0.98      | m1_connsp_2(X3,sK4,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_5747]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5766,plain,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.46/0.98      | m1_connsp_2(X0,sK4,sK7) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.46/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | v2_struct_0(sK1) = iProver_top
% 2.46/0.98      | v2_struct_0(sK3) = iProver_top
% 2.46/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2988,c_5748]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_41,negated_conjecture,
% 2.46/0.98      ( ~ v2_struct_0(sK1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_42,plain,
% 2.46/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_40,negated_conjecture,
% 2.46/0.98      ( v2_pre_topc(sK1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_43,plain,
% 2.46/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_39,negated_conjecture,
% 2.46/0.98      ( l1_pre_topc(sK1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_44,plain,
% 2.46/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_35,negated_conjecture,
% 2.46/0.98      ( ~ v2_struct_0(sK3) ),
% 2.46/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_48,plain,
% 2.46/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_32,negated_conjecture,
% 2.46/0.98      ( m1_pre_topc(sK4,sK1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_51,plain,
% 2.46/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_27,negated_conjecture,
% 2.46/0.98      ( m1_pre_topc(sK3,sK4) ),
% 2.46/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_56,plain,
% 2.46/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_25,negated_conjecture,
% 2.46/0.98      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.46/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_58,plain,
% 2.46/0.98      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_26,negated_conjecture,
% 2.46/0.98      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.46/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2908,plain,
% 2.46/0.98      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2951,plain,
% 2.46/0.98      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.46/0.98      inference(light_normalisation,[status(thm)],[c_2908,c_24]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_21,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.46/0.98      | ~ m1_connsp_2(X6,X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.46/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f107]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_19,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f105]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_219,plain,
% 2.46/0.98      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.46/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_21,c_19]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_220,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_219]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_825,plain,
% 2.46/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.46/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,X5)
% 2.46/0.98      | ~ m1_pre_topc(X4,X0)
% 2.46/0.98      | ~ m1_pre_topc(X4,X5)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.46/0.98      | ~ v1_funct_1(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X5)
% 2.46/0.98      | v2_struct_0(X4)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X5)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X5)
% 2.46/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.46/0.98      | sK5 != X2 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_220,c_30]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_826,plain,
% 2.46/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,X2)
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | ~ v1_funct_1(sK5)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_825]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_830,plain,
% 2.46/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_pre_topc(X0,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_826,c_31]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_831,plain,
% 2.46/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,X2)
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_830]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_872,plain,
% 2.46/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.46/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.46/0.98      | ~ m1_pre_topc(X3,X2)
% 2.46/0.98      | ~ m1_pre_topc(X0,X3)
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(X3)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.46/0.98      inference(forward_subsumption_resolution,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_831,c_18]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2893,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.46/0.98      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
% 2.46/0.98      | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.46/0.98      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X3) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(X3) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X3) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3795,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(equality_resolution,[status(thm)],[c_2893]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3265,plain,
% 2.46/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.46/0.98      | ~ r1_tmap_1(sK4,X1,sK5,X3)
% 2.46/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.46/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.46/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.46/0.98      | v2_struct_0(X0)
% 2.46/0.98      | v2_struct_0(X1)
% 2.46/0.98      | v2_struct_0(X2)
% 2.46/0.98      | v2_struct_0(sK4)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ l1_pre_topc(X2)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X2)
% 2.46/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.46/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_872]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3266,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_3265]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4187,plain,
% 2.46/0.98      ( v2_struct_0(X2) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.46/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_3795,c_50]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4188,plain,
% 2.46/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.46/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.46/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.46/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X2) = iProver_top
% 2.46/0.98      | l1_pre_topc(X0) != iProver_top
% 2.46/0.98      | l1_pre_topc(X2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) != iProver_top
% 2.46/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_4187]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4208,plain,
% 2.46/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(sK2) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.46/0.98      inference(equality_resolution,[status(thm)],[c_4188]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5657,plain,
% 2.46/0.98      ( v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_4208,c_45,c_46,c_47,c_54]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5658,plain,
% 2.46/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 2.46/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | v2_struct_0(X1) = iProver_top
% 2.46/0.98      | v2_struct_0(X0) = iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_5657]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_22,negated_conjecture,
% 2.46/0.98      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.46/0.98      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.46/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2911,plain,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3005,plain,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.46/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.46/0.98      inference(light_normalisation,[status(thm)],[c_2911,c_24]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5673,plain,
% 2.46/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.46/0.98      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.46/0.98      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | v2_struct_0(sK1) = iProver_top
% 2.46/0.98      | v2_struct_0(sK3) = iProver_top
% 2.46/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_5658,c_3005]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5796,plain,
% 2.46/0.98      ( m1_connsp_2(X0,sK4,sK7) != iProver_top
% 2.46/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.46/0.98      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_5766,c_42,c_43,c_44,c_48,c_51,c_56,c_58,c_2951,c_5673]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5806,plain,
% 2.46/0.98      ( m1_connsp_2(u1_struct_0(X0),sK4,sK7) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | l1_pre_topc(sK4) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2913,c_5796]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_7,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3274,plain,
% 2.46/0.98      ( ~ m1_pre_topc(sK4,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK4) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3674,plain,
% 2.46/0.98      ( ~ m1_pre_topc(sK4,sK1) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK1) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_3274]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3675,plain,
% 2.46/0.98      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.46/0.98      | l1_pre_topc(sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_3674]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5910,plain,
% 2.46/0.98      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | m1_connsp_2(u1_struct_0(X0),sK4,sK7) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_5806,c_44,c_51,c_3675]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5911,plain,
% 2.46/0.98      ( m1_connsp_2(u1_struct_0(X0),sK4,sK7) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_5910]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6160,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(X0),sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | r2_hidden(sK7,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | v2_struct_0(sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(sK4) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_6148,c_5911]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2905,plain,
% 2.46/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | v2_pre_topc(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2920,plain,
% 2.46/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X1) != iProver_top
% 2.46/0.98      | v2_pre_topc(X0) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4459,plain,
% 2.46/0.98      ( l1_pre_topc(sK1) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK4) = iProver_top
% 2.46/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2905,c_2920]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6208,plain,
% 2.46/0.98      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 2.46/0.98      | r2_hidden(sK7,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | v3_pre_topc(u1_struct_0(X0),sK4) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_6160,c_43,c_44,c_50,c_51,c_3675,c_4459]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6209,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(X0),sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.46/0.98      | r2_hidden(sK7,u1_struct_0(X0)) != iProver_top
% 2.46/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_6208]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6218,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4) != iProver_top
% 2.46/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.46/0.98      | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2923,c_6209]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2907,plain,
% 2.46/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2919,plain,
% 2.46/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(X1) != iProver_top
% 2.46/0.98      | l1_pre_topc(X0) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3897,plain,
% 2.46/0.98      ( l1_pre_topc(sK4) != iProver_top
% 2.46/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_2907,c_2919]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_16,plain,
% 2.46/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.46/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.46/0.98      | ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f104]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_228,plain,
% 2.46/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.46/0.98      | ~ v1_tsep_1(X0,X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_16,c_17]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_229,plain,
% 2.46/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.46/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.46/0.98      | ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1) ),
% 2.46/0.98      inference(renaming,[status(thm)],[c_228]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_28,negated_conjecture,
% 2.46/0.98      ( v1_tsep_1(sK3,sK4) ),
% 2.46/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_562,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.46/0.98      | ~ m1_pre_topc(X0,X1)
% 2.46/0.98      | ~ l1_pre_topc(X1)
% 2.46/0.98      | ~ v2_pre_topc(X1)
% 2.46/0.98      | sK4 != X1
% 2.46/0.98      | sK3 != X0 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_229,c_28]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_563,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.46/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.46/0.98      | ~ l1_pre_topc(sK4)
% 2.46/0.98      | ~ v2_pre_topc(sK4) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_562]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_565,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.46/0.98      | ~ l1_pre_topc(sK4)
% 2.46/0.98      | ~ v2_pre_topc(sK4) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_563,c_27]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2894,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
% 2.46/0.98      | l1_pre_topc(sK4) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_564,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
% 2.46/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.46/0.98      | l1_pre_topc(sK4) != iProver_top
% 2.46/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3771,plain,
% 2.46/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4) = iProver_top
% 2.46/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_2894,c_44,c_51,c_56,c_564,c_3675]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_6,plain,
% 2.46/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_8,plain,
% 2.46/0.98      ( v2_struct_0(X0)
% 2.46/0.98      | ~ l1_struct_0(X0)
% 2.46/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.46/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_521,plain,
% 2.46/0.99      ( v2_struct_0(X0)
% 2.46/0.99      | ~ l1_pre_topc(X0)
% 2.46/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.46/0.99      inference(resolution,[status(thm)],[c_6,c_8]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3436,plain,
% 2.46/0.99      ( v2_struct_0(sK3)
% 2.46/0.99      | ~ l1_pre_topc(sK3)
% 2.46/0.99      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_521]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3437,plain,
% 2.46/0.99      ( v2_struct_0(sK3) = iProver_top
% 2.46/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.46/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_3436]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3,plain,
% 2.46/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.46/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3279,plain,
% 2.46/0.99      ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.46/0.99      | r2_hidden(sK7,u1_struct_0(sK3))
% 2.46/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3280,plain,
% 2.46/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.46/0.99      | r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
% 2.46/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_3279]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(contradiction,plain,
% 2.46/0.99      ( $false ),
% 2.46/0.99      inference(minisat,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_6218,c_4459,c_3897,c_3771,c_3675,c_3437,c_3280,c_58,
% 2.46/0.99                 c_56,c_51,c_48,c_44,c_43]) ).
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  ------                               Statistics
% 2.46/0.99  
% 2.46/0.99  ------ General
% 2.46/0.99  
% 2.46/0.99  abstr_ref_over_cycles:                  0
% 2.46/0.99  abstr_ref_under_cycles:                 0
% 2.46/0.99  gc_basic_clause_elim:                   0
% 2.46/0.99  forced_gc_time:                         0
% 2.46/0.99  parsing_time:                           0.01
% 2.46/0.99  unif_index_cands_time:                  0.
% 2.46/0.99  unif_index_add_time:                    0.
% 2.46/0.99  orderings_time:                         0.
% 2.46/0.99  out_proof_time:                         0.015
% 2.46/0.99  total_time:                             0.205
% 2.46/0.99  num_of_symbols:                         58
% 2.46/0.99  num_of_terms:                           3381
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing
% 2.46/0.99  
% 2.46/0.99  num_of_splits:                          0
% 2.46/0.99  num_of_split_atoms:                     0
% 2.46/0.99  num_of_reused_defs:                     0
% 2.46/0.99  num_eq_ax_congr_red:                    23
% 2.46/0.99  num_of_sem_filtered_clauses:            1
% 2.46/0.99  num_of_subtypes:                        0
% 2.46/0.99  monotx_restored_types:                  0
% 2.46/0.99  sat_num_of_epr_types:                   0
% 2.46/0.99  sat_num_of_non_cyclic_types:            0
% 2.46/0.99  sat_guarded_non_collapsed_types:        0
% 2.46/0.99  num_pure_diseq_elim:                    0
% 2.46/0.99  simp_replaced_by:                       0
% 2.46/0.99  res_preprocessed:                       175
% 2.46/0.99  prep_upred:                             0
% 2.46/0.99  prep_unflattend:                        37
% 2.46/0.99  smt_new_axioms:                         0
% 2.46/0.99  pred_elim_cands:                        11
% 2.46/0.99  pred_elim:                              4
% 2.46/0.99  pred_elim_cl:                           6
% 2.46/0.99  pred_elim_cycles:                       12
% 2.46/0.99  merged_defs:                            8
% 2.46/0.99  merged_defs_ncl:                        0
% 2.46/0.99  bin_hyper_res:                          8
% 2.46/0.99  prep_cycles:                            4
% 2.46/0.99  pred_elim_time:                         0.035
% 2.46/0.99  splitting_time:                         0.
% 2.46/0.99  sem_filter_time:                        0.
% 2.46/0.99  monotx_time:                            0.001
% 2.46/0.99  subtype_inf_time:                       0.
% 2.46/0.99  
% 2.46/0.99  ------ Problem properties
% 2.46/0.99  
% 2.46/0.99  clauses:                                34
% 2.46/0.99  conjectures:                            17
% 2.46/0.99  epr:                                    18
% 2.46/0.99  horn:                                   25
% 2.46/0.99  ground:                                 18
% 2.46/0.99  unary:                                  16
% 2.46/0.99  binary:                                 2
% 2.46/0.99  lits:                                   125
% 2.46/0.99  lits_eq:                                6
% 2.46/0.99  fd_pure:                                0
% 2.46/0.99  fd_pseudo:                              0
% 2.46/0.99  fd_cond:                                0
% 2.46/0.99  fd_pseudo_cond:                         1
% 2.46/0.99  ac_symbols:                             0
% 2.46/0.99  
% 2.46/0.99  ------ Propositional Solver
% 2.46/0.99  
% 2.46/0.99  prop_solver_calls:                      27
% 2.46/0.99  prop_fast_solver_calls:                 2259
% 2.46/0.99  smt_solver_calls:                       0
% 2.46/0.99  smt_fast_solver_calls:                  0
% 2.46/0.99  prop_num_of_clauses:                    1516
% 2.46/0.99  prop_preprocess_simplified:             5792
% 2.46/0.99  prop_fo_subsumed:                       82
% 2.46/0.99  prop_solver_time:                       0.
% 2.46/0.99  smt_solver_time:                        0.
% 2.46/0.99  smt_fast_solver_time:                   0.
% 2.46/0.99  prop_fast_solver_time:                  0.
% 2.46/0.99  prop_unsat_core_time:                   0.
% 2.46/0.99  
% 2.46/0.99  ------ QBF
% 2.46/0.99  
% 2.46/0.99  qbf_q_res:                              0
% 2.46/0.99  qbf_num_tautologies:                    0
% 2.46/0.99  qbf_prep_cycles:                        0
% 2.46/0.99  
% 2.46/0.99  ------ BMC1
% 2.46/0.99  
% 2.46/0.99  bmc1_current_bound:                     -1
% 2.46/0.99  bmc1_last_solved_bound:                 -1
% 2.46/0.99  bmc1_unsat_core_size:                   -1
% 2.46/0.99  bmc1_unsat_core_parents_size:           -1
% 2.46/0.99  bmc1_merge_next_fun:                    0
% 2.46/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation
% 2.46/0.99  
% 2.46/0.99  inst_num_of_clauses:                    393
% 2.46/0.99  inst_num_in_passive:                    33
% 2.46/0.99  inst_num_in_active:                     326
% 2.46/0.99  inst_num_in_unprocessed:                34
% 2.46/0.99  inst_num_of_loops:                      370
% 2.46/0.99  inst_num_of_learning_restarts:          0
% 2.46/0.99  inst_num_moves_active_passive:          40
% 2.46/0.99  inst_lit_activity:                      0
% 2.46/0.99  inst_lit_activity_moves:                0
% 2.46/0.99  inst_num_tautologies:                   0
% 2.46/0.99  inst_num_prop_implied:                  0
% 2.46/0.99  inst_num_existing_simplified:           0
% 2.46/0.99  inst_num_eq_res_simplified:             0
% 2.46/0.99  inst_num_child_elim:                    0
% 2.46/0.99  inst_num_of_dismatching_blockings:      25
% 2.46/0.99  inst_num_of_non_proper_insts:           541
% 2.46/0.99  inst_num_of_duplicates:                 0
% 2.46/0.99  inst_inst_num_from_inst_to_res:         0
% 2.46/0.99  inst_dismatching_checking_time:         0.
% 2.46/0.99  
% 2.46/0.99  ------ Resolution
% 2.46/0.99  
% 2.46/0.99  res_num_of_clauses:                     0
% 2.46/0.99  res_num_in_passive:                     0
% 2.46/0.99  res_num_in_active:                      0
% 2.46/0.99  res_num_of_loops:                       179
% 2.46/0.99  res_forward_subset_subsumed:            98
% 2.46/0.99  res_backward_subset_subsumed:           2
% 2.46/0.99  res_forward_subsumed:                   0
% 2.46/0.99  res_backward_subsumed:                  0
% 2.46/0.99  res_forward_subsumption_resolution:     15
% 2.46/0.99  res_backward_subsumption_resolution:    0
% 2.46/0.99  res_clause_to_clause_subsumption:       373
% 2.46/0.99  res_orphan_elimination:                 0
% 2.46/0.99  res_tautology_del:                      92
% 2.46/0.99  res_num_eq_res_simplified:              0
% 2.46/0.99  res_num_sel_changes:                    0
% 2.46/0.99  res_moves_from_active_to_pass:          0
% 2.46/0.99  
% 2.46/0.99  ------ Superposition
% 2.46/0.99  
% 2.46/0.99  sup_time_total:                         0.
% 2.46/0.99  sup_time_generating:                    0.
% 2.46/0.99  sup_time_sim_full:                      0.
% 2.46/0.99  sup_time_sim_immed:                     0.
% 2.46/0.99  
% 2.46/0.99  sup_num_of_clauses:                     78
% 2.46/0.99  sup_num_in_active:                      72
% 2.46/0.99  sup_num_in_passive:                     6
% 2.46/0.99  sup_num_of_loops:                       72
% 2.46/0.99  sup_fw_superposition:                   34
% 2.46/0.99  sup_bw_superposition:                   17
% 2.46/0.99  sup_immediate_simplified:               4
% 2.46/0.99  sup_given_eliminated:                   0
% 2.46/0.99  comparisons_done:                       0
% 2.46/0.99  comparisons_avoided:                    0
% 2.46/0.99  
% 2.46/0.99  ------ Simplifications
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  sim_fw_subset_subsumed:                 4
% 2.46/0.99  sim_bw_subset_subsumed:                 2
% 2.46/0.99  sim_fw_subsumed:                        0
% 2.46/0.99  sim_bw_subsumed:                        0
% 2.46/0.99  sim_fw_subsumption_res:                 1
% 2.46/0.99  sim_bw_subsumption_res:                 0
% 2.46/0.99  sim_tautology_del:                      3
% 2.46/0.99  sim_eq_tautology_del:                   1
% 2.46/0.99  sim_eq_res_simp:                        0
% 2.46/0.99  sim_fw_demodulated:                     0
% 2.46/0.99  sim_bw_demodulated:                     0
% 2.46/0.99  sim_light_normalised:                   3
% 2.46/0.99  sim_joinable_taut:                      0
% 2.46/0.99  sim_joinable_simp:                      0
% 2.46/0.99  sim_ac_normalised:                      0
% 2.46/0.99  sim_smt_subsumption:                    0
% 2.46/0.99  
%------------------------------------------------------------------------------
