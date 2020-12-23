%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:20 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  221 (3284 expanded)
%              Number of clauses        :  141 ( 751 expanded)
%              Number of leaves         :   20 (1271 expanded)
%              Depth                    :   23
%              Number of atoms          : 1003 (46350 expanded)
%              Number of equality atoms :  217 (3751 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
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

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
              | ~ r2_hidden(X5,u1_struct_0(X2))
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK5)
        & ! [X5] :
            ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
            | ~ r2_hidden(X5,u1_struct_0(X2))
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(X2))
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK4,X2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK4,X5)
                | ~ r2_hidden(X5,u1_struct_0(X2))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK3),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(sK3))
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
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
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK2,X0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
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
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X1,sK1,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK1),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    & ! [X5] :
        ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK3))
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f41,f50,f49,f48,f47,f46])).

fof(f86,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f67,plain,(
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

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_835,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X3,X0),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_836,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_838,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_23,c_22,c_21])).

cnf(c_839,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(renaming,[status(thm)],[c_838])).

cnf(c_1237,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(subtyping,[status(esa)],[c_839])).

cnf(c_1830,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_70,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_72,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_557,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_558,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_559,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_438,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_439,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_441,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_29])).

cnf(c_571,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_441])).

cnf(c_572,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_573,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_840,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1257,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1885,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_1886,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1258,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1925,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_1926,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1259,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1957,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_1958,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1957])).

cnf(c_2835,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1830,c_37,c_43,c_44,c_45,c_72,c_559,c_573,c_840,c_1886,c_1926,c_1958])).

cnf(c_1256,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1811,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1260,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X0_55)
    | k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1807,plain,
    ( k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X1_54,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_2430,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X0_54) = k1_funct_1(sK5,X0_54)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1811,c_1807])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_584,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_585,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_586,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_3333,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X0_54) = k1_funct_1(sK5,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2430,c_46,c_47,c_573,c_586])).

cnf(c_3339,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_2835,c_3333])).

cnf(c_587,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_572])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_421,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_31,c_29,c_28])).

cnf(c_426,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_425])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK5,X2)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_426,c_392])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_587,c_483])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54) ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_1827,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_3730,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_2835,c_1827])).

cnf(c_1249,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_1818,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_2839,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_1818])).

cnf(c_1253,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1814,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_2431,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1807])).

cnf(c_595,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_596,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_597,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_3409,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2431,c_43,c_44,c_559,c_597])).

cnf(c_3724,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_2839,c_3409])).

cnf(c_3731,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_3730,c_3724])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_449,plain,
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
    | sK2 != X1
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_454,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_31,c_30,c_29])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_455,c_33])).

cnf(c_524,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_34,c_32])).

cnf(c_1247,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3) ),
    inference(subtyping,[status(esa)],[c_528])).

cnf(c_1820,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3)
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_2728,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1820])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1806,plain,
    ( k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_2094,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1806])).

cnf(c_2656,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_43])).

cnf(c_2731,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2728,c_2656])).

cnf(c_3804,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2731,c_43,c_44])).

cnf(c_3808,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3804,c_2835])).

cnf(c_3818,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(superposition,[status(thm)],[c_3808,c_3333])).

cnf(c_4278,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_3339,c_3339,c_3731,c_3804,c_3818])).

cnf(c_4,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_855,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
    | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_856,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_858,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_856,c_23,c_22,c_21])).

cnf(c_859,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(renaming,[status(thm)],[c_858])).

cnf(c_1236,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_1831,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_71,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2842,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1831,c_32,c_26,c_25,c_24,c_71,c_558,c_572,c_1236,c_1885,c_1925,c_1957])).

cnf(c_3807,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(demodulation,[status(thm)],[c_3804,c_2842])).

cnf(c_4280,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(demodulation,[status(thm)],[c_4278,c_3807])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_1250,plain,
    ( ~ m1_subset_1(X0_54,X0_55)
    | ~ v1_funct_1(X1_54)
    | ~ v1_relat_1(X1_54)
    | v1_xboole_0(X0_55)
    | k1_funct_1(k7_relat_1(X1_54,X0_55),X0_54) = k1_funct_1(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_1817,plain,
    ( k1_funct_1(k7_relat_1(X0_54,X0_55),X1_54) = k1_funct_1(X0_54,X1_54)
    | m1_subset_1(X1_54,X0_55) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_3820,plain,
    ( k1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(X0_54,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3808,c_1817])).

cnf(c_3822,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3820])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1264,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1803,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1802,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_2025,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1802])).

cnf(c_2366,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_2025])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4280,c_3822,c_2366,c_586,c_573,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.47/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.99  
% 3.47/0.99  ------  iProver source info
% 3.47/0.99  
% 3.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.99  git: non_committed_changes: false
% 3.47/0.99  git: last_make_outside_of_git: false
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  ------ Input Options
% 3.47/0.99  
% 3.47/0.99  --out_options                           all
% 3.47/0.99  --tptp_safe_out                         true
% 3.47/0.99  --problem_path                          ""
% 3.47/0.99  --include_path                          ""
% 3.47/0.99  --clausifier                            res/vclausify_rel
% 3.47/0.99  --clausifier_options                    ""
% 3.47/0.99  --stdin                                 false
% 3.47/0.99  --stats_out                             all
% 3.47/0.99  
% 3.47/0.99  ------ General Options
% 3.47/0.99  
% 3.47/0.99  --fof                                   false
% 3.47/0.99  --time_out_real                         305.
% 3.47/0.99  --time_out_virtual                      -1.
% 3.47/0.99  --symbol_type_check                     false
% 3.47/0.99  --clausify_out                          false
% 3.47/0.99  --sig_cnt_out                           false
% 3.47/0.99  --trig_cnt_out                          false
% 3.47/0.99  --trig_cnt_out_tolerance                1.
% 3.47/0.99  --trig_cnt_out_sk_spl                   false
% 3.47/0.99  --abstr_cl_out                          false
% 3.47/0.99  
% 3.47/0.99  ------ Global Options
% 3.47/0.99  
% 3.47/0.99  --schedule                              default
% 3.47/0.99  --add_important_lit                     false
% 3.47/0.99  --prop_solver_per_cl                    1000
% 3.47/0.99  --min_unsat_core                        false
% 3.47/0.99  --soft_assumptions                      false
% 3.47/0.99  --soft_lemma_size                       3
% 3.47/0.99  --prop_impl_unit_size                   0
% 3.47/0.99  --prop_impl_unit                        []
% 3.47/0.99  --share_sel_clauses                     true
% 3.47/0.99  --reset_solvers                         false
% 3.47/0.99  --bc_imp_inh                            [conj_cone]
% 3.47/0.99  --conj_cone_tolerance                   3.
% 3.47/0.99  --extra_neg_conj                        none
% 3.47/0.99  --large_theory_mode                     true
% 3.47/0.99  --prolific_symb_bound                   200
% 3.47/0.99  --lt_threshold                          2000
% 3.47/0.99  --clause_weak_htbl                      true
% 3.47/0.99  --gc_record_bc_elim                     false
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing Options
% 3.47/0.99  
% 3.47/0.99  --preprocessing_flag                    true
% 3.47/0.99  --time_out_prep_mult                    0.1
% 3.47/0.99  --splitting_mode                        input
% 3.47/0.99  --splitting_grd                         true
% 3.47/0.99  --splitting_cvd                         false
% 3.47/0.99  --splitting_cvd_svl                     false
% 3.47/0.99  --splitting_nvd                         32
% 3.47/0.99  --sub_typing                            true
% 3.47/0.99  --prep_gs_sim                           true
% 3.47/0.99  --prep_unflatten                        true
% 3.47/0.99  --prep_res_sim                          true
% 3.47/0.99  --prep_upred                            true
% 3.47/0.99  --prep_sem_filter                       exhaustive
% 3.47/0.99  --prep_sem_filter_out                   false
% 3.47/0.99  --pred_elim                             true
% 3.47/0.99  --res_sim_input                         true
% 3.47/0.99  --eq_ax_congr_red                       true
% 3.47/0.99  --pure_diseq_elim                       true
% 3.47/0.99  --brand_transform                       false
% 3.47/0.99  --non_eq_to_eq                          false
% 3.47/0.99  --prep_def_merge                        true
% 3.47/0.99  --prep_def_merge_prop_impl              false
% 3.47/0.99  --prep_def_merge_mbd                    true
% 3.47/0.99  --prep_def_merge_tr_red                 false
% 3.47/0.99  --prep_def_merge_tr_cl                  false
% 3.47/0.99  --smt_preprocessing                     true
% 3.47/0.99  --smt_ac_axioms                         fast
% 3.47/0.99  --preprocessed_out                      false
% 3.47/0.99  --preprocessed_stats                    false
% 3.47/0.99  
% 3.47/0.99  ------ Abstraction refinement Options
% 3.47/0.99  
% 3.47/0.99  --abstr_ref                             []
% 3.47/0.99  --abstr_ref_prep                        false
% 3.47/0.99  --abstr_ref_until_sat                   false
% 3.47/0.99  --abstr_ref_sig_restrict                funpre
% 3.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.99  --abstr_ref_under                       []
% 3.47/0.99  
% 3.47/0.99  ------ SAT Options
% 3.47/0.99  
% 3.47/0.99  --sat_mode                              false
% 3.47/0.99  --sat_fm_restart_options                ""
% 3.47/0.99  --sat_gr_def                            false
% 3.47/0.99  --sat_epr_types                         true
% 3.47/0.99  --sat_non_cyclic_types                  false
% 3.47/0.99  --sat_finite_models                     false
% 3.47/0.99  --sat_fm_lemmas                         false
% 3.47/0.99  --sat_fm_prep                           false
% 3.47/0.99  --sat_fm_uc_incr                        true
% 3.47/0.99  --sat_out_model                         small
% 3.47/0.99  --sat_out_clauses                       false
% 3.47/0.99  
% 3.47/0.99  ------ QBF Options
% 3.47/0.99  
% 3.47/0.99  --qbf_mode                              false
% 3.47/0.99  --qbf_elim_univ                         false
% 3.47/0.99  --qbf_dom_inst                          none
% 3.47/0.99  --qbf_dom_pre_inst                      false
% 3.47/0.99  --qbf_sk_in                             false
% 3.47/0.99  --qbf_pred_elim                         true
% 3.47/0.99  --qbf_split                             512
% 3.47/0.99  
% 3.47/0.99  ------ BMC1 Options
% 3.47/0.99  
% 3.47/0.99  --bmc1_incremental                      false
% 3.47/0.99  --bmc1_axioms                           reachable_all
% 3.47/0.99  --bmc1_min_bound                        0
% 3.47/0.99  --bmc1_max_bound                        -1
% 3.47/0.99  --bmc1_max_bound_default                -1
% 3.47/0.99  --bmc1_symbol_reachability              true
% 3.47/0.99  --bmc1_property_lemmas                  false
% 3.47/0.99  --bmc1_k_induction                      false
% 3.47/0.99  --bmc1_non_equiv_states                 false
% 3.47/0.99  --bmc1_deadlock                         false
% 3.47/0.99  --bmc1_ucm                              false
% 3.47/0.99  --bmc1_add_unsat_core                   none
% 3.47/0.99  --bmc1_unsat_core_children              false
% 3.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.99  --bmc1_out_stat                         full
% 3.47/0.99  --bmc1_ground_init                      false
% 3.47/0.99  --bmc1_pre_inst_next_state              false
% 3.47/0.99  --bmc1_pre_inst_state                   false
% 3.47/0.99  --bmc1_pre_inst_reach_state             false
% 3.47/0.99  --bmc1_out_unsat_core                   false
% 3.47/0.99  --bmc1_aig_witness_out                  false
% 3.47/0.99  --bmc1_verbose                          false
% 3.47/0.99  --bmc1_dump_clauses_tptp                false
% 3.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.99  --bmc1_dump_file                        -
% 3.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.99  --bmc1_ucm_extend_mode                  1
% 3.47/0.99  --bmc1_ucm_init_mode                    2
% 3.47/0.99  --bmc1_ucm_cone_mode                    none
% 3.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.99  --bmc1_ucm_relax_model                  4
% 3.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.99  --bmc1_ucm_layered_model                none
% 3.47/0.99  --bmc1_ucm_max_lemma_size               10
% 3.47/0.99  
% 3.47/0.99  ------ AIG Options
% 3.47/0.99  
% 3.47/0.99  --aig_mode                              false
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation Options
% 3.47/0.99  
% 3.47/0.99  --instantiation_flag                    true
% 3.47/0.99  --inst_sos_flag                         true
% 3.47/0.99  --inst_sos_phase                        true
% 3.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel_side                     num_symb
% 3.47/0.99  --inst_solver_per_active                1400
% 3.47/0.99  --inst_solver_calls_frac                1.
% 3.47/0.99  --inst_passive_queue_type               priority_queues
% 3.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.99  --inst_passive_queues_freq              [25;2]
% 3.47/0.99  --inst_dismatching                      true
% 3.47/0.99  --inst_eager_unprocessed_to_passive     true
% 3.47/0.99  --inst_prop_sim_given                   true
% 3.47/0.99  --inst_prop_sim_new                     false
% 3.47/0.99  --inst_subs_new                         false
% 3.47/0.99  --inst_eq_res_simp                      false
% 3.47/0.99  --inst_subs_given                       false
% 3.47/0.99  --inst_orphan_elimination               true
% 3.47/0.99  --inst_learning_loop_flag               true
% 3.47/0.99  --inst_learning_start                   3000
% 3.47/0.99  --inst_learning_factor                  2
% 3.47/0.99  --inst_start_prop_sim_after_learn       3
% 3.47/0.99  --inst_sel_renew                        solver
% 3.47/0.99  --inst_lit_activity_flag                true
% 3.47/0.99  --inst_restr_to_given                   false
% 3.47/0.99  --inst_activity_threshold               500
% 3.47/0.99  --inst_out_proof                        true
% 3.47/0.99  
% 3.47/0.99  ------ Resolution Options
% 3.47/0.99  
% 3.47/0.99  --resolution_flag                       true
% 3.47/0.99  --res_lit_sel                           adaptive
% 3.47/0.99  --res_lit_sel_side                      none
% 3.47/0.99  --res_ordering                          kbo
% 3.47/0.99  --res_to_prop_solver                    active
% 3.47/0.99  --res_prop_simpl_new                    false
% 3.47/0.99  --res_prop_simpl_given                  true
% 3.47/0.99  --res_passive_queue_type                priority_queues
% 3.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.99  --res_passive_queues_freq               [15;5]
% 3.47/0.99  --res_forward_subs                      full
% 3.47/0.99  --res_backward_subs                     full
% 3.47/0.99  --res_forward_subs_resolution           true
% 3.47/0.99  --res_backward_subs_resolution          true
% 3.47/0.99  --res_orphan_elimination                true
% 3.47/0.99  --res_time_limit                        2.
% 3.47/0.99  --res_out_proof                         true
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Options
% 3.47/0.99  
% 3.47/0.99  --superposition_flag                    true
% 3.47/0.99  --sup_passive_queue_type                priority_queues
% 3.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.99  --demod_completeness_check              fast
% 3.47/0.99  --demod_use_ground                      true
% 3.47/0.99  --sup_to_prop_solver                    passive
% 3.47/0.99  --sup_prop_simpl_new                    true
% 3.47/0.99  --sup_prop_simpl_given                  true
% 3.47/0.99  --sup_fun_splitting                     true
% 3.47/0.99  --sup_smt_interval                      50000
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Simplification Setup
% 3.47/0.99  
% 3.47/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.47/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.47/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.47/0.99  --sup_immed_triv                        [TrivRules]
% 3.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_immed_bw_main                     []
% 3.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_input_bw                          []
% 3.47/0.99  
% 3.47/0.99  ------ Combination Options
% 3.47/0.99  
% 3.47/0.99  --comb_res_mult                         3
% 3.47/0.99  --comb_sup_mult                         2
% 3.47/0.99  --comb_inst_mult                        10
% 3.47/0.99  
% 3.47/0.99  ------ Debug Options
% 3.47/0.99  
% 3.47/0.99  --dbg_backtrace                         false
% 3.47/0.99  --dbg_dump_prop_clauses                 false
% 3.47/0.99  --dbg_dump_prop_clauses_file            -
% 3.47/0.99  --dbg_out_stat                          false
% 3.47/0.99  ------ Parsing...
% 3.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  ------ Proving...
% 3.47/0.99  ------ Problem Properties 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  clauses                                 30
% 3.47/0.99  conjectures                             6
% 3.47/0.99  EPR                                     5
% 3.47/0.99  Horn                                    27
% 3.47/0.99  unary                                   13
% 3.47/0.99  binary                                  2
% 3.47/0.99  lits                                    95
% 3.47/0.99  lits eq                                 10
% 3.47/0.99  fd_pure                                 0
% 3.47/0.99  fd_pseudo                               0
% 3.47/0.99  fd_cond                                 0
% 3.47/0.99  fd_pseudo_cond                          0
% 3.47/0.99  AC symbols                              0
% 3.47/0.99  
% 3.47/0.99  ------ Schedule dynamic 5 is on 
% 3.47/0.99  
% 3.47/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  Current options:
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  ------ Input Options
% 3.47/0.99  
% 3.47/0.99  --out_options                           all
% 3.47/0.99  --tptp_safe_out                         true
% 3.47/0.99  --problem_path                          ""
% 3.47/0.99  --include_path                          ""
% 3.47/0.99  --clausifier                            res/vclausify_rel
% 3.47/0.99  --clausifier_options                    ""
% 3.47/0.99  --stdin                                 false
% 3.47/0.99  --stats_out                             all
% 3.47/0.99  
% 3.47/0.99  ------ General Options
% 3.47/0.99  
% 3.47/0.99  --fof                                   false
% 3.47/0.99  --time_out_real                         305.
% 3.47/0.99  --time_out_virtual                      -1.
% 3.47/0.99  --symbol_type_check                     false
% 3.47/0.99  --clausify_out                          false
% 3.47/0.99  --sig_cnt_out                           false
% 3.47/0.99  --trig_cnt_out                          false
% 3.47/0.99  --trig_cnt_out_tolerance                1.
% 3.47/0.99  --trig_cnt_out_sk_spl                   false
% 3.47/0.99  --abstr_cl_out                          false
% 3.47/0.99  
% 3.47/0.99  ------ Global Options
% 3.47/0.99  
% 3.47/0.99  --schedule                              default
% 3.47/0.99  --add_important_lit                     false
% 3.47/0.99  --prop_solver_per_cl                    1000
% 3.47/0.99  --min_unsat_core                        false
% 3.47/0.99  --soft_assumptions                      false
% 3.47/0.99  --soft_lemma_size                       3
% 3.47/0.99  --prop_impl_unit_size                   0
% 3.47/0.99  --prop_impl_unit                        []
% 3.47/0.99  --share_sel_clauses                     true
% 3.47/0.99  --reset_solvers                         false
% 3.47/0.99  --bc_imp_inh                            [conj_cone]
% 3.47/0.99  --conj_cone_tolerance                   3.
% 3.47/0.99  --extra_neg_conj                        none
% 3.47/0.99  --large_theory_mode                     true
% 3.47/0.99  --prolific_symb_bound                   200
% 3.47/0.99  --lt_threshold                          2000
% 3.47/0.99  --clause_weak_htbl                      true
% 3.47/0.99  --gc_record_bc_elim                     false
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing Options
% 3.47/0.99  
% 3.47/0.99  --preprocessing_flag                    true
% 3.47/0.99  --time_out_prep_mult                    0.1
% 3.47/0.99  --splitting_mode                        input
% 3.47/0.99  --splitting_grd                         true
% 3.47/0.99  --splitting_cvd                         false
% 3.47/0.99  --splitting_cvd_svl                     false
% 3.47/0.99  --splitting_nvd                         32
% 3.47/0.99  --sub_typing                            true
% 3.47/0.99  --prep_gs_sim                           true
% 3.47/0.99  --prep_unflatten                        true
% 3.47/0.99  --prep_res_sim                          true
% 3.47/0.99  --prep_upred                            true
% 3.47/0.99  --prep_sem_filter                       exhaustive
% 3.47/0.99  --prep_sem_filter_out                   false
% 3.47/0.99  --pred_elim                             true
% 3.47/0.99  --res_sim_input                         true
% 3.47/0.99  --eq_ax_congr_red                       true
% 3.47/0.99  --pure_diseq_elim                       true
% 3.47/0.99  --brand_transform                       false
% 3.47/0.99  --non_eq_to_eq                          false
% 3.47/0.99  --prep_def_merge                        true
% 3.47/0.99  --prep_def_merge_prop_impl              false
% 3.47/0.99  --prep_def_merge_mbd                    true
% 3.47/0.99  --prep_def_merge_tr_red                 false
% 3.47/0.99  --prep_def_merge_tr_cl                  false
% 3.47/0.99  --smt_preprocessing                     true
% 3.47/0.99  --smt_ac_axioms                         fast
% 3.47/0.99  --preprocessed_out                      false
% 3.47/0.99  --preprocessed_stats                    false
% 3.47/0.99  
% 3.47/0.99  ------ Abstraction refinement Options
% 3.47/0.99  
% 3.47/0.99  --abstr_ref                             []
% 3.47/0.99  --abstr_ref_prep                        false
% 3.47/0.99  --abstr_ref_until_sat                   false
% 3.47/0.99  --abstr_ref_sig_restrict                funpre
% 3.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.99  --abstr_ref_under                       []
% 3.47/0.99  
% 3.47/0.99  ------ SAT Options
% 3.47/0.99  
% 3.47/0.99  --sat_mode                              false
% 3.47/0.99  --sat_fm_restart_options                ""
% 3.47/0.99  --sat_gr_def                            false
% 3.47/0.99  --sat_epr_types                         true
% 3.47/0.99  --sat_non_cyclic_types                  false
% 3.47/0.99  --sat_finite_models                     false
% 3.47/0.99  --sat_fm_lemmas                         false
% 3.47/0.99  --sat_fm_prep                           false
% 3.47/0.99  --sat_fm_uc_incr                        true
% 3.47/0.99  --sat_out_model                         small
% 3.47/0.99  --sat_out_clauses                       false
% 3.47/0.99  
% 3.47/0.99  ------ QBF Options
% 3.47/0.99  
% 3.47/0.99  --qbf_mode                              false
% 3.47/0.99  --qbf_elim_univ                         false
% 3.47/0.99  --qbf_dom_inst                          none
% 3.47/0.99  --qbf_dom_pre_inst                      false
% 3.47/0.99  --qbf_sk_in                             false
% 3.47/0.99  --qbf_pred_elim                         true
% 3.47/0.99  --qbf_split                             512
% 3.47/0.99  
% 3.47/0.99  ------ BMC1 Options
% 3.47/0.99  
% 3.47/0.99  --bmc1_incremental                      false
% 3.47/0.99  --bmc1_axioms                           reachable_all
% 3.47/0.99  --bmc1_min_bound                        0
% 3.47/0.99  --bmc1_max_bound                        -1
% 3.47/0.99  --bmc1_max_bound_default                -1
% 3.47/0.99  --bmc1_symbol_reachability              true
% 3.47/0.99  --bmc1_property_lemmas                  false
% 3.47/0.99  --bmc1_k_induction                      false
% 3.47/0.99  --bmc1_non_equiv_states                 false
% 3.47/0.99  --bmc1_deadlock                         false
% 3.47/0.99  --bmc1_ucm                              false
% 3.47/0.99  --bmc1_add_unsat_core                   none
% 3.47/0.99  --bmc1_unsat_core_children              false
% 3.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.99  --bmc1_out_stat                         full
% 3.47/0.99  --bmc1_ground_init                      false
% 3.47/0.99  --bmc1_pre_inst_next_state              false
% 3.47/0.99  --bmc1_pre_inst_state                   false
% 3.47/0.99  --bmc1_pre_inst_reach_state             false
% 3.47/0.99  --bmc1_out_unsat_core                   false
% 3.47/0.99  --bmc1_aig_witness_out                  false
% 3.47/0.99  --bmc1_verbose                          false
% 3.47/0.99  --bmc1_dump_clauses_tptp                false
% 3.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.99  --bmc1_dump_file                        -
% 3.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.99  --bmc1_ucm_extend_mode                  1
% 3.47/0.99  --bmc1_ucm_init_mode                    2
% 3.47/0.99  --bmc1_ucm_cone_mode                    none
% 3.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.99  --bmc1_ucm_relax_model                  4
% 3.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.99  --bmc1_ucm_layered_model                none
% 3.47/0.99  --bmc1_ucm_max_lemma_size               10
% 3.47/0.99  
% 3.47/0.99  ------ AIG Options
% 3.47/0.99  
% 3.47/0.99  --aig_mode                              false
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation Options
% 3.47/0.99  
% 3.47/0.99  --instantiation_flag                    true
% 3.47/0.99  --inst_sos_flag                         true
% 3.47/0.99  --inst_sos_phase                        true
% 3.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel_side                     none
% 3.47/0.99  --inst_solver_per_active                1400
% 3.47/0.99  --inst_solver_calls_frac                1.
% 3.47/0.99  --inst_passive_queue_type               priority_queues
% 3.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.99  --inst_passive_queues_freq              [25;2]
% 3.47/0.99  --inst_dismatching                      true
% 3.47/0.99  --inst_eager_unprocessed_to_passive     true
% 3.47/0.99  --inst_prop_sim_given                   true
% 3.47/0.99  --inst_prop_sim_new                     false
% 3.47/0.99  --inst_subs_new                         false
% 3.47/0.99  --inst_eq_res_simp                      false
% 3.47/0.99  --inst_subs_given                       false
% 3.47/0.99  --inst_orphan_elimination               true
% 3.47/0.99  --inst_learning_loop_flag               true
% 3.47/0.99  --inst_learning_start                   3000
% 3.47/0.99  --inst_learning_factor                  2
% 3.47/0.99  --inst_start_prop_sim_after_learn       3
% 3.47/0.99  --inst_sel_renew                        solver
% 3.47/0.99  --inst_lit_activity_flag                true
% 3.47/0.99  --inst_restr_to_given                   false
% 3.47/0.99  --inst_activity_threshold               500
% 3.47/0.99  --inst_out_proof                        true
% 3.47/0.99  
% 3.47/0.99  ------ Resolution Options
% 3.47/0.99  
% 3.47/0.99  --resolution_flag                       false
% 3.47/0.99  --res_lit_sel                           adaptive
% 3.47/0.99  --res_lit_sel_side                      none
% 3.47/0.99  --res_ordering                          kbo
% 3.47/0.99  --res_to_prop_solver                    active
% 3.47/0.99  --res_prop_simpl_new                    false
% 3.47/0.99  --res_prop_simpl_given                  true
% 3.47/0.99  --res_passive_queue_type                priority_queues
% 3.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.99  --res_passive_queues_freq               [15;5]
% 3.47/0.99  --res_forward_subs                      full
% 3.47/0.99  --res_backward_subs                     full
% 3.47/0.99  --res_forward_subs_resolution           true
% 3.47/0.99  --res_backward_subs_resolution          true
% 3.47/0.99  --res_orphan_elimination                true
% 3.47/0.99  --res_time_limit                        2.
% 3.47/0.99  --res_out_proof                         true
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Options
% 3.47/0.99  
% 3.47/0.99  --superposition_flag                    true
% 3.47/0.99  --sup_passive_queue_type                priority_queues
% 3.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.99  --demod_completeness_check              fast
% 3.47/0.99  --demod_use_ground                      true
% 3.47/0.99  --sup_to_prop_solver                    passive
% 3.47/0.99  --sup_prop_simpl_new                    true
% 3.47/0.99  --sup_prop_simpl_given                  true
% 3.47/0.99  --sup_fun_splitting                     true
% 3.47/0.99  --sup_smt_interval                      50000
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Simplification Setup
% 3.47/0.99  
% 3.47/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.47/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.47/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.47/0.99  --sup_immed_triv                        [TrivRules]
% 3.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_immed_bw_main                     []
% 3.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_input_bw                          []
% 3.47/0.99  
% 3.47/0.99  ------ Combination Options
% 3.47/0.99  
% 3.47/0.99  --comb_res_mult                         3
% 3.47/0.99  --comb_sup_mult                         2
% 3.47/0.99  --comb_inst_mult                        10
% 3.47/0.99  
% 3.47/0.99  ------ Debug Options
% 3.47/0.99  
% 3.47/0.99  --dbg_backtrace                         false
% 3.47/0.99  --dbg_dump_prop_clauses                 false
% 3.47/0.99  --dbg_dump_prop_clauses_file            -
% 3.47/0.99  --dbg_out_stat                          false
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS status Theorem for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  fof(f5,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f22,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.47/0.99    inference(ennf_transformation,[],[f5])).
% 3.47/0.99  
% 3.47/0.99  fof(f23,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.47/0.99    inference(flattening,[],[f22])).
% 3.47/0.99  
% 3.47/0.99  fof(f42,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.47/0.99    inference(nnf_transformation,[],[f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f43,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.47/0.99    inference(rectify,[],[f42])).
% 3.47/0.99  
% 3.47/0.99  fof(f44,plain,(
% 3.47/0.99    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f45,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.47/0.99  
% 3.47/0.99  fof(f57,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f45])).
% 3.47/0.99  
% 3.47/0.99  fof(f15,conjecture,(
% 3.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f16,negated_conjecture,(
% 3.47/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 3.47/0.99    inference(negated_conjecture,[],[f15])).
% 3.47/0.99  
% 3.47/0.99  fof(f40,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f16])).
% 3.47/0.99  
% 3.47/0.99  fof(f41,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f40])).
% 3.47/0.99  
% 3.47/0.99  fof(f50,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK5) & ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f49,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK4,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f48,plain,(
% 3.47/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK3),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f47,plain,(
% 3.47/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK2,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f46,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X1,sK1,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK1),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f51,plain,(
% 3.47/0.99    ((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) & ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f41,f50,f49,f48,f47,f46])).
% 3.47/0.99  
% 3.47/0.99  fof(f86,plain,(
% 3.47/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f82,plain,(
% 3.47/0.99    v1_funct_1(sK5)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f83,plain,(
% 3.47/0.99    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f84,plain,(
% 3.47/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f73,plain,(
% 3.47/0.99    l1_pre_topc(sK1)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f79,plain,(
% 3.47/0.99    v1_funct_1(sK4)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f80,plain,(
% 3.47/0.99    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f81,plain,(
% 3.47/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f9,axiom,(
% 3.47/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f30,plain,(
% 3.47/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f9])).
% 3.47/0.99  
% 3.47/0.99  fof(f63,plain,(
% 3.47/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f30])).
% 3.47/0.99  
% 3.47/0.99  fof(f76,plain,(
% 3.47/0.99    l1_pre_topc(sK2)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f10,axiom,(
% 3.47/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f31,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f10])).
% 3.47/0.99  
% 3.47/0.99  fof(f64,plain,(
% 3.47/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f31])).
% 3.47/0.99  
% 3.47/0.99  fof(f78,plain,(
% 3.47/0.99    m1_pre_topc(sK3,sK2)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f14,axiom,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f38,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f14])).
% 3.47/0.99  
% 3.47/0.99  fof(f39,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f68,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f39])).
% 3.47/0.99  
% 3.47/0.99  fof(f69,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f39])).
% 3.47/0.99  
% 3.47/0.99  fof(f70,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f39])).
% 3.47/0.99  
% 3.47/0.99  fof(f8,axiom,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f28,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f8])).
% 3.47/0.99  
% 3.47/0.99  fof(f29,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.47/0.99    inference(flattening,[],[f28])).
% 3.47/0.99  
% 3.47/0.99  fof(f62,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f29])).
% 3.47/0.99  
% 3.47/0.99  fof(f11,axiom,(
% 3.47/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f32,plain,(
% 3.47/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f11])).
% 3.47/0.99  
% 3.47/0.99  fof(f33,plain,(
% 3.47/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f32])).
% 3.47/0.99  
% 3.47/0.99  fof(f65,plain,(
% 3.47/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f33])).
% 3.47/0.99  
% 3.47/0.99  fof(f77,plain,(
% 3.47/0.99    ~v2_struct_0(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f12,axiom,(
% 3.47/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f34,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f12])).
% 3.47/0.99  
% 3.47/0.99  fof(f35,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f34])).
% 3.47/0.99  
% 3.47/0.99  fof(f66,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f35])).
% 3.47/0.99  
% 3.47/0.99  fof(f74,plain,(
% 3.47/0.99    ~v2_struct_0(sK2)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f1,axiom,(
% 3.47/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f17,plain,(
% 3.47/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.47/0.99    inference(ennf_transformation,[],[f1])).
% 3.47/0.99  
% 3.47/0.99  fof(f18,plain,(
% 3.47/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.47/0.99    inference(flattening,[],[f17])).
% 3.47/0.99  
% 3.47/0.99  fof(f52,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f18])).
% 3.47/0.99  
% 3.47/0.99  fof(f85,plain,(
% 3.47/0.99    ( ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f13,axiom,(
% 3.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f36,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f13])).
% 3.47/0.99  
% 3.47/0.99  fof(f37,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f36])).
% 3.47/0.99  
% 3.47/0.99  fof(f67,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f37])).
% 3.47/0.99  
% 3.47/0.99  fof(f75,plain,(
% 3.47/0.99    v2_pre_topc(sK2)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f72,plain,(
% 3.47/0.99    v2_pre_topc(sK1)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f71,plain,(
% 3.47/0.99    ~v2_struct_0(sK1)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f7,axiom,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f26,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.47/0.99    inference(ennf_transformation,[],[f7])).
% 3.47/0.99  
% 3.47/0.99  fof(f27,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.47/0.99    inference(flattening,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  fof(f61,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f27])).
% 3.47/0.99  
% 3.47/0.99  fof(f58,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f45])).
% 3.47/0.99  
% 3.47/0.99  fof(f4,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f20,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.47/0.99    inference(ennf_transformation,[],[f4])).
% 3.47/0.99  
% 3.47/0.99  fof(f21,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(flattening,[],[f20])).
% 3.47/0.99  
% 3.47/0.99  fof(f55,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f21])).
% 3.47/0.99  
% 3.47/0.99  fof(f3,axiom,(
% 3.47/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f54,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f3])).
% 3.47/0.99  
% 3.47/0.99  fof(f2,axiom,(
% 3.47/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f19,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f2])).
% 3.47/0.99  
% 3.47/0.99  fof(f53,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f19])).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5,plain,
% 3.47/0.99      ( r2_funct_2(X0,X1,X2,X3)
% 3.47/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.47/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.47/0.99      | m1_subset_1(sK0(X0,X2,X3),X0)
% 3.47/0.99      | ~ v1_funct_1(X2)
% 3.47/0.99      | ~ v1_funct_1(X3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_19,negated_conjecture,
% 3.47/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
% 3.47/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_835,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ v1_funct_2(X3,X1,X2)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | m1_subset_1(sK0(X1,X3,X0),X1)
% 3.47/0.99      | ~ v1_funct_1(X3)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
% 3.47/0.99      | u1_struct_0(sK1) != X2
% 3.47/0.99      | u1_struct_0(sK3) != X1
% 3.47/0.99      | sK5 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_836,plain,
% 3.47/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | ~ v1_funct_1(sK5) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_835]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_23,negated_conjecture,
% 3.47/0.99      ( v1_funct_1(sK5) ),
% 3.47/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_22,negated_conjecture,
% 3.47/0.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_21,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_838,plain,
% 3.47/0.99      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_836,c_23,c_22,c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_839,plain,
% 3.47/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 3.47/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_838]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1237,plain,
% 3.47/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 3.47/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_839]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1830,plain,
% 3.47/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
% 3.47/0.99      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_32,negated_conjecture,
% 3.47/0.99      ( l1_pre_topc(sK1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_37,plain,
% 3.47/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_26,negated_conjecture,
% 3.47/0.99      ( v1_funct_1(sK4) ),
% 3.47/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_43,plain,
% 3.47/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_25,negated_conjecture,
% 3.47/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_44,plain,
% 3.47/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_24,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_45,plain,
% 3.47/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_11,plain,
% 3.47/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_70,plain,
% 3.47/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_72,plain,
% 3.47/0.99      ( l1_pre_topc(sK1) != iProver_top
% 3.47/0.99      | l1_struct_0(sK1) = iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_70]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_29,negated_conjecture,
% 3.47/0.99      ( l1_pre_topc(sK2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_557,plain,
% 3.47/0.99      ( l1_struct_0(X0) | sK2 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_558,plain,
% 3.47/0.99      ( l1_struct_0(sK2) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_559,plain,
% 3.47/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_12,plain,
% 3.47/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_27,negated_conjecture,
% 3.47/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_438,plain,
% 3.47/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK3 != X1 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_439,plain,
% 3.47/0.99      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_438]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_441,plain,
% 3.47/0.99      ( l1_pre_topc(sK3) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_439,c_29]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_571,plain,
% 3.47/0.99      ( l1_struct_0(X0) | sK3 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_441]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_572,plain,
% 3.47/0.99      ( l1_struct_0(sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_571]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_573,plain,
% 3.47/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_840,plain,
% 3.47/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
% 3.47/0.99      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_18,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.47/0.99      | ~ l1_struct_0(X1)
% 3.47/0.99      | ~ l1_struct_0(X3)
% 3.47/0.99      | ~ l1_struct_0(X2)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1257,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.47/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.47/0.99      | ~ l1_struct_0(X1_56)
% 3.47/0.99      | ~ l1_struct_0(X2_56)
% 3.47/0.99      | ~ l1_struct_0(X0_56)
% 3.47/0.99      | ~ v1_funct_1(X0_54)
% 3.47/0.99      | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1885,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.47/0.99      | ~ l1_struct_0(sK2)
% 3.47/0.99      | ~ l1_struct_0(sK1)
% 3.47/0.99      | ~ l1_struct_0(sK3)
% 3.47/0.99      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | ~ v1_funct_1(sK4) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1257]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1886,plain,
% 3.47/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | l1_struct_0(sK2) != iProver_top
% 3.47/0.99      | l1_struct_0(sK1) != iProver_top
% 3.47/0.99      | l1_struct_0(sK3) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_17,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.47/0.99      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.47/0.99      | ~ l1_struct_0(X1)
% 3.47/0.99      | ~ l1_struct_0(X3)
% 3.47/0.99      | ~ l1_struct_0(X2)
% 3.47/0.99      | ~ v1_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1258,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.47/0.99      | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
% 3.47/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.47/0.99      | ~ l1_struct_0(X1_56)
% 3.47/0.99      | ~ l1_struct_0(X2_56)
% 3.47/0.99      | ~ l1_struct_0(X0_56)
% 3.47/0.99      | ~ v1_funct_1(X0_54) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1925,plain,
% 3.47/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.47/0.99      | ~ l1_struct_0(sK2)
% 3.47/0.99      | ~ l1_struct_0(sK1)
% 3.47/0.99      | ~ l1_struct_0(sK3)
% 3.47/0.99      | ~ v1_funct_1(sK4) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1258]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1926,plain,
% 3.47/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 3.47/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | l1_struct_0(sK2) != iProver_top
% 3.47/0.99      | l1_struct_0(sK1) != iProver_top
% 3.47/0.99      | l1_struct_0(sK3) != iProver_top
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_16,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.47/0.99      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.47/0.99      | ~ l1_struct_0(X1)
% 3.47/0.99      | ~ l1_struct_0(X3)
% 3.47/0.99      | ~ l1_struct_0(X2)
% 3.47/0.99      | ~ v1_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1259,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.47/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.47/0.99      | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 3.47/0.99      | ~ l1_struct_0(X1_56)
% 3.47/0.99      | ~ l1_struct_0(X2_56)
% 3.47/0.99      | ~ l1_struct_0(X0_56)
% 3.47/0.99      | ~ v1_funct_1(X0_54) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1957,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.47/0.99      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.47/0.99      | ~ l1_struct_0(sK2)
% 3.47/0.99      | ~ l1_struct_0(sK1)
% 3.47/0.99      | ~ l1_struct_0(sK3)
% 3.47/0.99      | ~ v1_funct_1(sK4) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1259]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1958,plain,
% 3.47/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 3.47/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | l1_struct_0(sK2) != iProver_top
% 3.47/0.99      | l1_struct_0(sK1) != iProver_top
% 3.47/0.99      | l1_struct_0(sK3) != iProver_top
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1957]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2835,plain,
% 3.47/0.99      ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_1830,c_37,c_43,c_44,c_45,c_72,c_559,c_573,c_840,
% 3.47/0.99                 c_1886,c_1926,c_1958]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1256,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1811,plain,
% 3.47/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_10,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ m1_subset_1(X3,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | v1_xboole_0(X1)
% 3.47/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1260,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.47/0.99      | ~ m1_subset_1(X1_54,X0_55)
% 3.47/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.47/0.99      | ~ v1_funct_1(X0_54)
% 3.47/0.99      | v1_xboole_0(X0_55)
% 3.47/0.99      | k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1807,plain,
% 3.47/0.99      ( k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54)
% 3.47/0.99      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.47/0.99      | m1_subset_1(X1_54,X0_55) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_54) != iProver_top
% 3.47/0.99      | v1_xboole_0(X0_55) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2430,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X0_54) = k1_funct_1(sK5,X0_54)
% 3.47/0.99      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 3.47/0.99      | v1_funct_1(sK5) != iProver_top
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1811,c_1807]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_46,plain,
% 3.47/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_47,plain,
% 3.47/0.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_13,plain,
% 3.47/0.99      ( v2_struct_0(X0)
% 3.47/0.99      | ~ l1_struct_0(X0)
% 3.47/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_28,negated_conjecture,
% 3.47/0.99      ( ~ v2_struct_0(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_584,plain,
% 3.47/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_585,plain,
% 3.47/0.99      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_584]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_586,plain,
% 3.47/0.99      ( l1_struct_0(sK3) != iProver_top
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3333,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X0_54) = k1_funct_1(sK5,X0_54)
% 3.47/0.99      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2430,c_46,c_47,c_573,c_586]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3339,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2835,c_3333]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_587,plain,
% 3.47/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_585,c_572]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_14,plain,
% 3.47/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.47/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | v2_struct_0(X0)
% 3.47/0.99      | ~ l1_pre_topc(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_420,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.47/0.99      | m1_subset_1(X0,u1_struct_0(X2))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | v2_struct_0(X2)
% 3.47/0.99      | ~ l1_pre_topc(X2)
% 3.47/0.99      | sK2 != X2
% 3.47/0.99      | sK3 != X1 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_421,plain,
% 3.47/0.99      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.47/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | v2_struct_0(sK2)
% 3.47/0.99      | v2_struct_0(sK3)
% 3.47/0.99      | ~ l1_pre_topc(sK2) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_31,negated_conjecture,
% 3.47/0.99      ( ~ v2_struct_0(sK2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_425,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_421,c_31,c_29,c_28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_426,plain,
% 3.47/0.99      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.47/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_425]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_0,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_20,negated_conjecture,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.47/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.47/0.99      | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_391,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.47/0.99      | v1_xboole_0(X1)
% 3.47/0.99      | X2 != X0
% 3.47/0.99      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK5,X2)
% 3.47/0.99      | u1_struct_0(sK3) != X1 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_392,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.47/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.47/0.99      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_391]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_483,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.47/0.99      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.47/0.99      inference(backward_subsumption_resolution,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_426,c_392]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_618,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.47/0.99      inference(backward_subsumption_resolution,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_587,c_483]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1240,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 3.47/0.99      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_618]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1827,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54)
% 3.47/0.99      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3730,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2835,c_1827]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1249,plain,
% 3.47/0.99      ( m1_subset_1(X0_54,u1_struct_0(sK2))
% 3.47/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_426]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1818,plain,
% 3.47/0.99      ( m1_subset_1(X0_54,u1_struct_0(sK2)) = iProver_top
% 3.47/0.99      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2839,plain,
% 3.47/0.99      ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK2)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2835,c_1818]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1253,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1814,plain,
% 3.47/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2431,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
% 3.47/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1814,c_1807]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_595,plain,
% 3.47/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_596,plain,
% 3.47/0.99      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_595]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_597,plain,
% 3.47/0.99      ( l1_struct_0(sK2) != iProver_top
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3409,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
% 3.47/0.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2431,c_43,c_44,c_559,c_597]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3724,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2839,c_3409]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3731,plain,
% 3.47/0.99      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(light_normalisation,[status(thm)],[c_3730,c_3724]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_15,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.47/0.99      | ~ m1_pre_topc(X3,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.47/0.99      | ~ v2_pre_topc(X2)
% 3.47/0.99      | ~ v2_pre_topc(X1)
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | v2_struct_0(X2)
% 3.47/0.99      | ~ l1_pre_topc(X1)
% 3.47/0.99      | ~ l1_pre_topc(X2)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_449,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.47/0.99      | ~ v2_pre_topc(X1)
% 3.47/0.99      | ~ v2_pre_topc(X2)
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | v2_struct_0(X2)
% 3.47/0.99      | ~ l1_pre_topc(X1)
% 3.47/0.99      | ~ l1_pre_topc(X2)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.47/0.99      | sK2 != X1
% 3.47/0.99      | sK3 != X3 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_450,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.47/0.99      | ~ v2_pre_topc(X1)
% 3.47/0.99      | ~ v2_pre_topc(sK2)
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | v2_struct_0(sK2)
% 3.47/0.99      | ~ l1_pre_topc(X1)
% 3.47/0.99      | ~ l1_pre_topc(sK2)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_449]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_30,negated_conjecture,
% 3.47/0.99      ( v2_pre_topc(sK2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_454,plain,
% 3.47/0.99      ( ~ l1_pre_topc(X1)
% 3.47/0.99      | ~ v2_pre_topc(X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.47/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_450,c_31,c_30,c_29]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_455,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.47/0.99      | ~ v2_pre_topc(X1)
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ l1_pre_topc(X1)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_454]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_33,negated_conjecture,
% 3.47/0.99      ( v2_pre_topc(sK1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_523,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ l1_pre_topc(X1)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
% 3.47/0.99      | sK1 != X1 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_455,c_33]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_524,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.47/0.99      | v2_struct_0(sK1)
% 3.47/0.99      | ~ l1_pre_topc(sK1)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_523]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_34,negated_conjecture,
% 3.47/0.99      ( ~ v2_struct_0(sK1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_528,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_524,c_34,c_32]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1247,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.47/0.99      | ~ v1_funct_1(X0_54)
% 3.47/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_528]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1820,plain,
% 3.47/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3)
% 3.47/0.99      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_54) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2728,plain,
% 3.47/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 3.47/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1814,c_1820]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1261,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.47/0.99      | ~ v1_funct_1(X0_54)
% 3.47/0.99      | k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1806,plain,
% 3.47/0.99      ( k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55)
% 3.47/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_54) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2094,plain,
% 3.47/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55)
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1814,c_1806]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2656,plain,
% 3.47/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2094,c_43]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2731,plain,
% 3.47/0.99      ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
% 3.47/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_2728,c_2656]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3804,plain,
% 3.47/0.99      ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2731,c_43,c_44]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3808,plain,
% 3.47/0.99      ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_3804,c_2835]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3818,plain,
% 3.47/0.99      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3808,c_3333]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4278,plain,
% 3.47/0.99      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.47/0.99      inference(light_normalisation,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_3339,c_3339,c_3731,c_3804,c_3818]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4,plain,
% 3.47/0.99      ( r2_funct_2(X0,X1,X2,X3)
% 3.47/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.47/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.47/0.99      | ~ v1_funct_1(X2)
% 3.47/0.99      | ~ v1_funct_1(X3)
% 3.47/0.99      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_855,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ v1_funct_2(X3,X1,X2)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X3)
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
% 3.47/0.99      | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
% 3.47/0.99      | u1_struct_0(sK1) != X2
% 3.47/0.99      | u1_struct_0(sK3) != X1
% 3.47/0.99      | sK5 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_856,plain,
% 3.47/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | ~ v1_funct_1(sK5)
% 3.47/0.99      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_855]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_858,plain,
% 3.47/0.99      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_856,c_23,c_22,c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_859,plain,
% 3.47/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_858]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1236,plain,
% 3.47/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.47/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.47/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.47/0.99      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_859]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1831,plain,
% 3.47/0.99      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5))
% 3.47/0.99      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.47/0.99      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_71,plain,
% 3.47/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2842,plain,
% 3.47/0.99      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_1831,c_32,c_26,c_25,c_24,c_71,c_558,c_572,c_1236,
% 3.47/0.99                 c_1885,c_1925,c_1957]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3807,plain,
% 3.47/0.99      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_3804,c_2842]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4280,plain,
% 3.47/0.99      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_4278,c_3807]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1)
% 3.47/0.99      | ~ v1_funct_1(X2)
% 3.47/0.99      | ~ v1_relat_1(X2)
% 3.47/0.99      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_371,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,X1)
% 3.47/0.99      | ~ v1_funct_1(X2)
% 3.47/0.99      | ~ v1_relat_1(X2)
% 3.47/0.99      | v1_xboole_0(X1)
% 3.47/0.99      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 3.47/0.99      inference(resolution,[status(thm)],[c_0,c_3]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1250,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0_54,X0_55)
% 3.47/0.99      | ~ v1_funct_1(X1_54)
% 3.47/0.99      | ~ v1_relat_1(X1_54)
% 3.47/0.99      | v1_xboole_0(X0_55)
% 3.47/0.99      | k1_funct_1(k7_relat_1(X1_54,X0_55),X0_54) = k1_funct_1(X1_54,X0_54) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_371]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1817,plain,
% 3.47/0.99      ( k1_funct_1(k7_relat_1(X0_54,X0_55),X1_54) = k1_funct_1(X0_54,X1_54)
% 3.47/0.99      | m1_subset_1(X1_54,X0_55) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_54) != iProver_top
% 3.47/0.99      | v1_relat_1(X0_54) != iProver_top
% 3.47/0.99      | v1_xboole_0(X0_55) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3820,plain,
% 3.47/0.99      ( k1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(X0_54,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 3.47/0.99      | v1_funct_1(X0_54) != iProver_top
% 3.47/0.99      | v1_relat_1(X0_54) != iProver_top
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3808,c_1817]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3822,plain,
% 3.47/0.99      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 3.47/0.99      | v1_funct_1(sK4) != iProver_top
% 3.47/0.99      | v1_relat_1(sK4) != iProver_top
% 3.47/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_3820]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1264,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1803,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.99      | ~ v1_relat_1(X1)
% 3.47/0.99      | v1_relat_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1265,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 3.47/0.99      | ~ v1_relat_1(X1_54)
% 3.47/0.99      | v1_relat_1(X0_54) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1802,plain,
% 3.47/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 3.47/0.99      | v1_relat_1(X1_54) != iProver_top
% 3.47/0.99      | v1_relat_1(X0_54) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2025,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
% 3.47/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1814,c_1802]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2366,plain,
% 3.47/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1803,c_2025]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(contradiction,plain,
% 3.47/0.99      ( $false ),
% 3.47/0.99      inference(minisat,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4280,c_3822,c_2366,c_586,c_573,c_43]) ).
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  ------                               Statistics
% 3.47/0.99  
% 3.47/0.99  ------ General
% 3.47/0.99  
% 3.47/0.99  abstr_ref_over_cycles:                  0
% 3.47/0.99  abstr_ref_under_cycles:                 0
% 3.47/0.99  gc_basic_clause_elim:                   0
% 3.47/0.99  forced_gc_time:                         0
% 3.47/0.99  parsing_time:                           0.015
% 3.47/0.99  unif_index_cands_time:                  0.
% 3.47/0.99  unif_index_add_time:                    0.
% 3.47/0.99  orderings_time:                         0.
% 3.47/0.99  out_proof_time:                         0.016
% 3.47/0.99  total_time:                             0.252
% 3.47/0.99  num_of_symbols:                         58
% 3.47/0.99  num_of_terms:                           4886
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing
% 3.47/0.99  
% 3.47/0.99  num_of_splits:                          0
% 3.47/0.99  num_of_split_atoms:                     0
% 3.47/0.99  num_of_reused_defs:                     0
% 3.47/0.99  num_eq_ax_congr_red:                    22
% 3.47/0.99  num_of_sem_filtered_clauses:            1
% 3.47/0.99  num_of_subtypes:                        4
% 3.47/0.99  monotx_restored_types:                  0
% 3.47/0.99  sat_num_of_epr_types:                   0
% 3.47/0.99  sat_num_of_non_cyclic_types:            0
% 3.47/0.99  sat_guarded_non_collapsed_types:        0
% 3.47/0.99  num_pure_diseq_elim:                    0
% 3.47/0.99  simp_replaced_by:                       0
% 3.47/0.99  res_preprocessed:                       160
% 3.47/0.99  prep_upred:                             0
% 3.47/0.99  prep_unflattend:                        36
% 3.47/0.99  smt_new_axioms:                         0
% 3.47/0.99  pred_elim_cands:                        6
% 3.47/0.99  pred_elim:                              6
% 3.47/0.99  pred_elim_cl:                           5
% 3.47/0.99  pred_elim_cycles:                       9
% 3.47/0.99  merged_defs:                            0
% 3.47/0.99  merged_defs_ncl:                        0
% 3.47/0.99  bin_hyper_res:                          0
% 3.47/0.99  prep_cycles:                            4
% 3.47/0.99  pred_elim_time:                         0.017
% 3.47/0.99  splitting_time:                         0.
% 3.47/0.99  sem_filter_time:                        0.
% 3.47/0.99  monotx_time:                            0.
% 3.47/0.99  subtype_inf_time:                       0.
% 3.47/0.99  
% 3.47/0.99  ------ Problem properties
% 3.47/0.99  
% 3.47/0.99  clauses:                                30
% 3.47/0.99  conjectures:                            6
% 3.47/0.99  epr:                                    5
% 3.47/0.99  horn:                                   27
% 3.47/0.99  ground:                                 14
% 3.47/0.99  unary:                                  13
% 3.47/0.99  binary:                                 2
% 3.47/0.99  lits:                                   95
% 3.47/0.99  lits_eq:                                10
% 3.47/0.99  fd_pure:                                0
% 3.47/0.99  fd_pseudo:                              0
% 3.47/0.99  fd_cond:                                0
% 3.47/0.99  fd_pseudo_cond:                         0
% 3.47/0.99  ac_symbols:                             0
% 3.47/0.99  
% 3.47/0.99  ------ Propositional Solver
% 3.47/0.99  
% 3.47/0.99  prop_solver_calls:                      33
% 3.47/0.99  prop_fast_solver_calls:                 1397
% 3.47/0.99  smt_solver_calls:                       0
% 3.47/0.99  smt_fast_solver_calls:                  0
% 3.47/0.99  prop_num_of_clauses:                    1686
% 3.47/0.99  prop_preprocess_simplified:             5117
% 3.47/0.99  prop_fo_subsumed:                       63
% 3.47/0.99  prop_solver_time:                       0.
% 3.47/0.99  smt_solver_time:                        0.
% 3.47/0.99  smt_fast_solver_time:                   0.
% 3.47/0.99  prop_fast_solver_time:                  0.
% 3.47/0.99  prop_unsat_core_time:                   0.
% 3.47/0.99  
% 3.47/0.99  ------ QBF
% 3.47/0.99  
% 3.47/0.99  qbf_q_res:                              0
% 3.47/0.99  qbf_num_tautologies:                    0
% 3.47/0.99  qbf_prep_cycles:                        0
% 3.47/0.99  
% 3.47/0.99  ------ BMC1
% 3.47/0.99  
% 3.47/0.99  bmc1_current_bound:                     -1
% 3.47/0.99  bmc1_last_solved_bound:                 -1
% 3.47/0.99  bmc1_unsat_core_size:                   -1
% 3.47/0.99  bmc1_unsat_core_parents_size:           -1
% 3.47/0.99  bmc1_merge_next_fun:                    0
% 3.47/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation
% 3.47/0.99  
% 3.47/0.99  inst_num_of_clauses:                    399
% 3.47/0.99  inst_num_in_passive:                    23
% 3.47/0.99  inst_num_in_active:                     299
% 3.47/0.99  inst_num_in_unprocessed:                78
% 3.47/0.99  inst_num_of_loops:                      340
% 3.47/0.99  inst_num_of_learning_restarts:          0
% 3.47/0.99  inst_num_moves_active_passive:          33
% 3.47/0.99  inst_lit_activity:                      0
% 3.47/0.99  inst_lit_activity_moves:                0
% 3.47/0.99  inst_num_tautologies:                   0
% 3.47/0.99  inst_num_prop_implied:                  0
% 3.47/0.99  inst_num_existing_simplified:           0
% 3.47/0.99  inst_num_eq_res_simplified:             0
% 3.47/0.99  inst_num_child_elim:                    0
% 3.47/0.99  inst_num_of_dismatching_blockings:      110
% 3.47/0.99  inst_num_of_non_proper_insts:           584
% 3.47/0.99  inst_num_of_duplicates:                 0
% 3.47/0.99  inst_inst_num_from_inst_to_res:         0
% 3.47/0.99  inst_dismatching_checking_time:         0.
% 3.47/0.99  
% 3.47/0.99  ------ Resolution
% 3.47/0.99  
% 3.47/0.99  res_num_of_clauses:                     0
% 3.47/0.99  res_num_in_passive:                     0
% 3.47/0.99  res_num_in_active:                      0
% 3.47/0.99  res_num_of_loops:                       164
% 3.47/0.99  res_forward_subset_subsumed:            75
% 3.47/0.99  res_backward_subset_subsumed:           2
% 3.47/0.99  res_forward_subsumed:                   0
% 3.47/0.99  res_backward_subsumed:                  0
% 3.47/0.99  res_forward_subsumption_resolution:     0
% 3.47/0.99  res_backward_subsumption_resolution:    2
% 3.47/0.99  res_clause_to_clause_subsumption:       195
% 3.47/0.99  res_orphan_elimination:                 0
% 3.47/0.99  res_tautology_del:                      80
% 3.47/0.99  res_num_eq_res_simplified:              0
% 3.47/0.99  res_num_sel_changes:                    0
% 3.47/0.99  res_moves_from_active_to_pass:          0
% 3.47/0.99  
% 3.47/0.99  ------ Superposition
% 3.47/0.99  
% 3.47/0.99  sup_time_total:                         0.
% 3.47/0.99  sup_time_generating:                    0.
% 3.47/0.99  sup_time_sim_full:                      0.
% 3.47/0.99  sup_time_sim_immed:                     0.
% 3.47/0.99  
% 3.47/0.99  sup_num_of_clauses:                     119
% 3.47/0.99  sup_num_in_active:                      54
% 3.47/0.99  sup_num_in_passive:                     65
% 3.47/0.99  sup_num_of_loops:                       67
% 3.47/0.99  sup_fw_superposition:                   56
% 3.47/0.99  sup_bw_superposition:                   43
% 3.47/0.99  sup_immediate_simplified:               9
% 3.47/0.99  sup_given_eliminated:                   0
% 3.47/0.99  comparisons_done:                       0
% 3.47/0.99  comparisons_avoided:                    0
% 3.47/0.99  
% 3.47/0.99  ------ Simplifications
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  sim_fw_subset_subsumed:                 0
% 3.47/0.99  sim_bw_subset_subsumed:                 4
% 3.47/0.99  sim_fw_subsumed:                        3
% 3.47/0.99  sim_bw_subsumed:                        2
% 3.47/0.99  sim_fw_subsumption_res:                 0
% 3.47/0.99  sim_bw_subsumption_res:                 0
% 3.47/0.99  sim_tautology_del:                      0
% 3.47/0.99  sim_eq_tautology_del:                   2
% 3.47/0.99  sim_eq_res_simp:                        0
% 3.47/0.99  sim_fw_demodulated:                     1
% 3.47/0.99  sim_bw_demodulated:                     9
% 3.47/0.99  sim_light_normalised:                   6
% 3.47/0.99  sim_joinable_taut:                      0
% 3.47/0.99  sim_joinable_simp:                      0
% 3.47/0.99  sim_ac_normalised:                      0
% 3.47/0.99  sim_smt_subsumption:                    0
% 3.47/0.99  
%------------------------------------------------------------------------------
