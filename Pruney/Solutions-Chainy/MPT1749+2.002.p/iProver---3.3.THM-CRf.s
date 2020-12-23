%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:20 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  211 (2241 expanded)
%              Number of clauses        :  133 ( 505 expanded)
%              Number of leaves         :   19 ( 875 expanded)
%              Depth                    :   22
%              Number of atoms          : 1002 (32007 expanded)
%              Number of equality atoms :  201 (2572 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f21])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

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
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f39])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f49,f48,f47,f46,f45])).

fof(f84,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f35])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_874,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X3,X0),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_875,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_874])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_877,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_875,c_22,c_21,c_20])).

cnf(c_878,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(renaming,[status(thm)],[c_877])).

cnf(c_1294,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(subtyping,[status(esa)],[c_878])).

cnf(c_1852,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_69,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_71,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_596,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_597,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_598,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_477,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_478,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_28])).

cnf(c_610,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_480])).

cnf(c_611,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_612,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_879,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1314,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2175,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,X0_56))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_2385,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_2386,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2385])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1315,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2185,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,X0_56),u1_struct_0(X0_56),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_2768,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_2769,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2768])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1316,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X2_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2195,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_56)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_3072,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_3073,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3072])).

cnf(c_3569,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_36,c_42,c_43,c_44,c_71,c_598,c_612,c_879,c_2386,c_2769,c_3073])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_623,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_624,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_626,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_611])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_460,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_30,c_28,c_27])).

cnf(c_465,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK5,X2)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_465,c_405])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_626,c_522])).

cnf(c_1297,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54) ),
    inference(subtyping,[status(esa)],[c_657])).

cnf(c_1849,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_4715,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_3569,c_1849])).

cnf(c_1310,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1836,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_488,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_489,plain,
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
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_493,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_30,c_29,c_28])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_562,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_32])).

cnf(c_563,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_567,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_33,c_31])).

cnf(c_1304,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3) ),
    inference(subtyping,[status(esa)],[c_567])).

cnf(c_1842,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3)
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_3381,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1842])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1318,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1828,plain,
    ( k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_2503,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1828])).

cnf(c_2155,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_3292,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2503,c_25,c_23,c_2155])).

cnf(c_3415,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3381,c_3292])).

cnf(c_5016,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3415,c_42,c_43])).

cnf(c_1306,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_1840,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1306])).

cnf(c_3574,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_1840])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1317,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X0_55)
    | k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1829,plain,
    ( k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X1_54,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_2616,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1829])).

cnf(c_634,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_635,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_636,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_3711,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2616,c_42,c_43,c_598,c_636])).

cnf(c_4574,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_3574,c_3711])).

cnf(c_5205,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_4574,c_5016])).

cnf(c_5286,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_4715,c_5016,c_5205])).

cnf(c_3,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_894,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
    | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_895,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_897,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_22,c_21,c_20])).

cnf(c_898,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(renaming,[status(thm)],[c_897])).

cnf(c_1293,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(subtyping,[status(esa)],[c_898])).

cnf(c_1853,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_70,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3577,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1853,c_31,c_25,c_24,c_23,c_70,c_597,c_611,c_1293,c_2385,c_2768,c_3072])).

cnf(c_5020,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(demodulation,[status(thm)],[c_5016,c_3577])).

cnf(c_5289,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(demodulation,[status(thm)],[c_5286,c_5020])).

cnf(c_5021,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5016,c_3569])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(X0_54,X0_55)
    | ~ v1_relat_1(X1_54)
    | ~ v1_funct_1(X1_54)
    | v1_xboole_0(X0_55)
    | k1_funct_1(k7_relat_1(X1_54,X0_55),X0_54) = k1_funct_1(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_1839,plain,
    ( k1_funct_1(k7_relat_1(X0_54,X0_55),X1_54) = k1_funct_1(X0_54,X1_54)
    | m1_subset_1(X1_54,X0_55) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_5103,plain,
    ( k1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(X0_54,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5021,c_1839])).

cnf(c_5117,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5103])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_2113,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_625,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5289,c_5117,c_2113,c_625,c_612,c_44,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.11/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/0.98  
% 3.11/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.98  
% 3.11/0.98  ------  iProver source info
% 3.11/0.98  
% 3.11/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.98  git: non_committed_changes: false
% 3.11/0.98  git: last_make_outside_of_git: false
% 3.11/0.98  
% 3.11/0.98  ------ 
% 3.11/0.98  
% 3.11/0.98  ------ Input Options
% 3.11/0.98  
% 3.11/0.98  --out_options                           all
% 3.11/0.98  --tptp_safe_out                         true
% 3.11/0.98  --problem_path                          ""
% 3.11/0.98  --include_path                          ""
% 3.11/0.98  --clausifier                            res/vclausify_rel
% 3.11/0.98  --clausifier_options                    --mode clausify
% 3.11/0.98  --stdin                                 false
% 3.11/0.98  --stats_out                             all
% 3.11/0.98  
% 3.11/0.98  ------ General Options
% 3.11/0.98  
% 3.11/0.98  --fof                                   false
% 3.11/0.98  --time_out_real                         305.
% 3.11/0.98  --time_out_virtual                      -1.
% 3.11/0.98  --symbol_type_check                     false
% 3.11/0.98  --clausify_out                          false
% 3.11/0.98  --sig_cnt_out                           false
% 3.11/0.98  --trig_cnt_out                          false
% 3.11/0.98  --trig_cnt_out_tolerance                1.
% 3.11/0.98  --trig_cnt_out_sk_spl                   false
% 3.11/0.98  --abstr_cl_out                          false
% 3.11/0.98  
% 3.11/0.98  ------ Global Options
% 3.11/0.98  
% 3.11/0.98  --schedule                              default
% 3.11/0.98  --add_important_lit                     false
% 3.11/0.98  --prop_solver_per_cl                    1000
% 3.11/0.98  --min_unsat_core                        false
% 3.11/0.98  --soft_assumptions                      false
% 3.11/0.98  --soft_lemma_size                       3
% 3.11/0.98  --prop_impl_unit_size                   0
% 3.11/0.98  --prop_impl_unit                        []
% 3.11/0.98  --share_sel_clauses                     true
% 3.11/0.98  --reset_solvers                         false
% 3.11/0.98  --bc_imp_inh                            [conj_cone]
% 3.11/0.98  --conj_cone_tolerance                   3.
% 3.11/0.98  --extra_neg_conj                        none
% 3.11/0.98  --large_theory_mode                     true
% 3.11/0.98  --prolific_symb_bound                   200
% 3.11/0.98  --lt_threshold                          2000
% 3.11/0.98  --clause_weak_htbl                      true
% 3.11/0.98  --gc_record_bc_elim                     false
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing Options
% 3.11/0.98  
% 3.11/0.98  --preprocessing_flag                    true
% 3.11/0.98  --time_out_prep_mult                    0.1
% 3.11/0.98  --splitting_mode                        input
% 3.11/0.98  --splitting_grd                         true
% 3.11/0.98  --splitting_cvd                         false
% 3.11/0.98  --splitting_cvd_svl                     false
% 3.11/0.98  --splitting_nvd                         32
% 3.11/0.98  --sub_typing                            true
% 3.11/0.98  --prep_gs_sim                           true
% 3.11/0.98  --prep_unflatten                        true
% 3.11/0.98  --prep_res_sim                          true
% 3.11/0.98  --prep_upred                            true
% 3.11/0.98  --prep_sem_filter                       exhaustive
% 3.11/0.98  --prep_sem_filter_out                   false
% 3.11/0.98  --pred_elim                             true
% 3.11/0.98  --res_sim_input                         true
% 3.11/0.98  --eq_ax_congr_red                       true
% 3.11/0.98  --pure_diseq_elim                       true
% 3.11/0.98  --brand_transform                       false
% 3.11/0.98  --non_eq_to_eq                          false
% 3.11/0.98  --prep_def_merge                        true
% 3.11/0.98  --prep_def_merge_prop_impl              false
% 3.11/0.98  --prep_def_merge_mbd                    true
% 3.11/0.98  --prep_def_merge_tr_red                 false
% 3.11/0.98  --prep_def_merge_tr_cl                  false
% 3.11/0.98  --smt_preprocessing                     true
% 3.11/0.98  --smt_ac_axioms                         fast
% 3.11/0.98  --preprocessed_out                      false
% 3.11/0.98  --preprocessed_stats                    false
% 3.11/0.98  
% 3.11/0.98  ------ Abstraction refinement Options
% 3.11/0.98  
% 3.11/0.98  --abstr_ref                             []
% 3.11/0.98  --abstr_ref_prep                        false
% 3.11/0.98  --abstr_ref_until_sat                   false
% 3.11/0.98  --abstr_ref_sig_restrict                funpre
% 3.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.98  --abstr_ref_under                       []
% 3.11/0.98  
% 3.11/0.98  ------ SAT Options
% 3.11/0.98  
% 3.11/0.98  --sat_mode                              false
% 3.11/0.98  --sat_fm_restart_options                ""
% 3.11/0.98  --sat_gr_def                            false
% 3.11/0.98  --sat_epr_types                         true
% 3.11/0.98  --sat_non_cyclic_types                  false
% 3.11/0.98  --sat_finite_models                     false
% 3.11/0.98  --sat_fm_lemmas                         false
% 3.11/0.98  --sat_fm_prep                           false
% 3.11/0.98  --sat_fm_uc_incr                        true
% 3.11/0.98  --sat_out_model                         small
% 3.11/0.98  --sat_out_clauses                       false
% 3.11/0.98  
% 3.11/0.98  ------ QBF Options
% 3.11/0.98  
% 3.11/0.98  --qbf_mode                              false
% 3.11/0.98  --qbf_elim_univ                         false
% 3.11/0.98  --qbf_dom_inst                          none
% 3.11/0.98  --qbf_dom_pre_inst                      false
% 3.11/0.98  --qbf_sk_in                             false
% 3.11/0.98  --qbf_pred_elim                         true
% 3.11/0.98  --qbf_split                             512
% 3.11/0.98  
% 3.11/0.98  ------ BMC1 Options
% 3.11/0.98  
% 3.11/0.98  --bmc1_incremental                      false
% 3.11/0.98  --bmc1_axioms                           reachable_all
% 3.11/0.98  --bmc1_min_bound                        0
% 3.11/0.98  --bmc1_max_bound                        -1
% 3.11/0.98  --bmc1_max_bound_default                -1
% 3.11/0.98  --bmc1_symbol_reachability              true
% 3.11/0.98  --bmc1_property_lemmas                  false
% 3.11/0.98  --bmc1_k_induction                      false
% 3.11/0.98  --bmc1_non_equiv_states                 false
% 3.11/0.98  --bmc1_deadlock                         false
% 3.11/0.98  --bmc1_ucm                              false
% 3.11/0.98  --bmc1_add_unsat_core                   none
% 3.11/0.98  --bmc1_unsat_core_children              false
% 3.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.98  --bmc1_out_stat                         full
% 3.11/0.98  --bmc1_ground_init                      false
% 3.11/0.98  --bmc1_pre_inst_next_state              false
% 3.11/0.98  --bmc1_pre_inst_state                   false
% 3.11/0.98  --bmc1_pre_inst_reach_state             false
% 3.11/0.98  --bmc1_out_unsat_core                   false
% 3.11/0.98  --bmc1_aig_witness_out                  false
% 3.11/0.98  --bmc1_verbose                          false
% 3.11/0.98  --bmc1_dump_clauses_tptp                false
% 3.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.98  --bmc1_dump_file                        -
% 3.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.98  --bmc1_ucm_extend_mode                  1
% 3.11/0.98  --bmc1_ucm_init_mode                    2
% 3.11/0.98  --bmc1_ucm_cone_mode                    none
% 3.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.98  --bmc1_ucm_relax_model                  4
% 3.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.98  --bmc1_ucm_layered_model                none
% 3.11/0.98  --bmc1_ucm_max_lemma_size               10
% 3.11/0.98  
% 3.11/0.98  ------ AIG Options
% 3.11/0.98  
% 3.11/0.98  --aig_mode                              false
% 3.11/0.98  
% 3.11/0.98  ------ Instantiation Options
% 3.11/0.98  
% 3.11/0.98  --instantiation_flag                    true
% 3.11/0.98  --inst_sos_flag                         false
% 3.11/0.98  --inst_sos_phase                        true
% 3.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel_side                     num_symb
% 3.11/0.98  --inst_solver_per_active                1400
% 3.11/0.98  --inst_solver_calls_frac                1.
% 3.11/0.98  --inst_passive_queue_type               priority_queues
% 3.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.98  --inst_passive_queues_freq              [25;2]
% 3.11/0.98  --inst_dismatching                      true
% 3.11/0.98  --inst_eager_unprocessed_to_passive     true
% 3.11/0.98  --inst_prop_sim_given                   true
% 3.11/0.98  --inst_prop_sim_new                     false
% 3.11/0.98  --inst_subs_new                         false
% 3.11/0.98  --inst_eq_res_simp                      false
% 3.11/0.98  --inst_subs_given                       false
% 3.11/0.98  --inst_orphan_elimination               true
% 3.11/0.98  --inst_learning_loop_flag               true
% 3.11/0.98  --inst_learning_start                   3000
% 3.11/0.98  --inst_learning_factor                  2
% 3.11/0.98  --inst_start_prop_sim_after_learn       3
% 3.11/0.98  --inst_sel_renew                        solver
% 3.11/0.98  --inst_lit_activity_flag                true
% 3.11/0.98  --inst_restr_to_given                   false
% 3.11/0.98  --inst_activity_threshold               500
% 3.11/0.98  --inst_out_proof                        true
% 3.11/0.98  
% 3.11/0.98  ------ Resolution Options
% 3.11/0.98  
% 3.11/0.98  --resolution_flag                       true
% 3.11/0.98  --res_lit_sel                           adaptive
% 3.11/0.98  --res_lit_sel_side                      none
% 3.11/0.98  --res_ordering                          kbo
% 3.11/0.98  --res_to_prop_solver                    active
% 3.11/0.98  --res_prop_simpl_new                    false
% 3.11/0.98  --res_prop_simpl_given                  true
% 3.11/0.98  --res_passive_queue_type                priority_queues
% 3.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.98  --res_passive_queues_freq               [15;5]
% 3.11/0.98  --res_forward_subs                      full
% 3.11/0.98  --res_backward_subs                     full
% 3.11/0.98  --res_forward_subs_resolution           true
% 3.11/0.98  --res_backward_subs_resolution          true
% 3.11/0.98  --res_orphan_elimination                true
% 3.11/0.98  --res_time_limit                        2.
% 3.11/0.98  --res_out_proof                         true
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Options
% 3.11/0.98  
% 3.11/0.98  --superposition_flag                    true
% 3.11/0.98  --sup_passive_queue_type                priority_queues
% 3.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.98  --demod_completeness_check              fast
% 3.11/0.98  --demod_use_ground                      true
% 3.11/0.98  --sup_to_prop_solver                    passive
% 3.11/0.98  --sup_prop_simpl_new                    true
% 3.11/0.98  --sup_prop_simpl_given                  true
% 3.11/0.98  --sup_fun_splitting                     false
% 3.11/0.98  --sup_smt_interval                      50000
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Simplification Setup
% 3.11/0.98  
% 3.11/0.98  --sup_indices_passive                   []
% 3.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_full_bw                           [BwDemod]
% 3.11/0.98  --sup_immed_triv                        [TrivRules]
% 3.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_immed_bw_main                     []
% 3.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.98  
% 3.11/0.98  ------ Combination Options
% 3.11/0.98  
% 3.11/0.98  --comb_res_mult                         3
% 3.11/0.98  --comb_sup_mult                         2
% 3.11/0.98  --comb_inst_mult                        10
% 3.11/0.98  
% 3.11/0.98  ------ Debug Options
% 3.11/0.98  
% 3.11/0.98  --dbg_backtrace                         false
% 3.11/0.98  --dbg_dump_prop_clauses                 false
% 3.11/0.98  --dbg_dump_prop_clauses_file            -
% 3.11/0.98  --dbg_out_stat                          false
% 3.11/0.98  ------ Parsing...
% 3.11/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.98  ------ Proving...
% 3.11/0.98  ------ Problem Properties 
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  clauses                                 29
% 3.11/0.98  conjectures                             6
% 3.11/0.98  EPR                                     5
% 3.11/0.98  Horn                                    26
% 3.11/0.98  unary                                   12
% 3.11/0.98  binary                                  3
% 3.11/0.98  lits                                    93
% 3.11/0.98  lits eq                                 10
% 3.11/0.98  fd_pure                                 0
% 3.11/0.98  fd_pseudo                               0
% 3.11/0.98  fd_cond                                 0
% 3.11/0.98  fd_pseudo_cond                          0
% 3.11/0.98  AC symbols                              0
% 3.11/0.98  
% 3.11/0.98  ------ Schedule dynamic 5 is on 
% 3.11/0.98  
% 3.11/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  ------ 
% 3.11/0.98  Current options:
% 3.11/0.98  ------ 
% 3.11/0.98  
% 3.11/0.98  ------ Input Options
% 3.11/0.98  
% 3.11/0.98  --out_options                           all
% 3.11/0.98  --tptp_safe_out                         true
% 3.11/0.98  --problem_path                          ""
% 3.11/0.98  --include_path                          ""
% 3.11/0.98  --clausifier                            res/vclausify_rel
% 3.11/0.98  --clausifier_options                    --mode clausify
% 3.11/0.98  --stdin                                 false
% 3.11/0.98  --stats_out                             all
% 3.11/0.98  
% 3.11/0.98  ------ General Options
% 3.11/0.98  
% 3.11/0.98  --fof                                   false
% 3.11/0.98  --time_out_real                         305.
% 3.11/0.98  --time_out_virtual                      -1.
% 3.11/0.98  --symbol_type_check                     false
% 3.11/0.98  --clausify_out                          false
% 3.11/0.98  --sig_cnt_out                           false
% 3.11/0.98  --trig_cnt_out                          false
% 3.11/0.98  --trig_cnt_out_tolerance                1.
% 3.11/0.98  --trig_cnt_out_sk_spl                   false
% 3.11/0.98  --abstr_cl_out                          false
% 3.11/0.98  
% 3.11/0.98  ------ Global Options
% 3.11/0.98  
% 3.11/0.98  --schedule                              default
% 3.11/0.98  --add_important_lit                     false
% 3.11/0.98  --prop_solver_per_cl                    1000
% 3.11/0.98  --min_unsat_core                        false
% 3.11/0.98  --soft_assumptions                      false
% 3.11/0.98  --soft_lemma_size                       3
% 3.11/0.98  --prop_impl_unit_size                   0
% 3.11/0.98  --prop_impl_unit                        []
% 3.11/0.98  --share_sel_clauses                     true
% 3.11/0.98  --reset_solvers                         false
% 3.11/0.98  --bc_imp_inh                            [conj_cone]
% 3.11/0.98  --conj_cone_tolerance                   3.
% 3.11/0.98  --extra_neg_conj                        none
% 3.11/0.98  --large_theory_mode                     true
% 3.11/0.98  --prolific_symb_bound                   200
% 3.11/0.98  --lt_threshold                          2000
% 3.11/0.98  --clause_weak_htbl                      true
% 3.11/0.98  --gc_record_bc_elim                     false
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing Options
% 3.11/0.98  
% 3.11/0.98  --preprocessing_flag                    true
% 3.11/0.98  --time_out_prep_mult                    0.1
% 3.11/0.98  --splitting_mode                        input
% 3.11/0.98  --splitting_grd                         true
% 3.11/0.98  --splitting_cvd                         false
% 3.11/0.98  --splitting_cvd_svl                     false
% 3.11/0.98  --splitting_nvd                         32
% 3.11/0.98  --sub_typing                            true
% 3.11/0.98  --prep_gs_sim                           true
% 3.11/0.98  --prep_unflatten                        true
% 3.11/0.98  --prep_res_sim                          true
% 3.11/0.98  --prep_upred                            true
% 3.11/0.98  --prep_sem_filter                       exhaustive
% 3.11/0.98  --prep_sem_filter_out                   false
% 3.11/0.98  --pred_elim                             true
% 3.11/0.98  --res_sim_input                         true
% 3.11/0.98  --eq_ax_congr_red                       true
% 3.11/0.98  --pure_diseq_elim                       true
% 3.11/0.98  --brand_transform                       false
% 3.11/0.98  --non_eq_to_eq                          false
% 3.11/0.98  --prep_def_merge                        true
% 3.11/0.98  --prep_def_merge_prop_impl              false
% 3.11/0.98  --prep_def_merge_mbd                    true
% 3.11/0.98  --prep_def_merge_tr_red                 false
% 3.11/0.98  --prep_def_merge_tr_cl                  false
% 3.11/0.98  --smt_preprocessing                     true
% 3.11/0.98  --smt_ac_axioms                         fast
% 3.11/0.98  --preprocessed_out                      false
% 3.11/0.98  --preprocessed_stats                    false
% 3.11/0.98  
% 3.11/0.98  ------ Abstraction refinement Options
% 3.11/0.98  
% 3.11/0.98  --abstr_ref                             []
% 3.11/0.98  --abstr_ref_prep                        false
% 3.11/0.98  --abstr_ref_until_sat                   false
% 3.11/0.98  --abstr_ref_sig_restrict                funpre
% 3.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.98  --abstr_ref_under                       []
% 3.11/0.98  
% 3.11/0.98  ------ SAT Options
% 3.11/0.98  
% 3.11/0.98  --sat_mode                              false
% 3.11/0.98  --sat_fm_restart_options                ""
% 3.11/0.98  --sat_gr_def                            false
% 3.11/0.98  --sat_epr_types                         true
% 3.11/0.98  --sat_non_cyclic_types                  false
% 3.11/0.98  --sat_finite_models                     false
% 3.11/0.98  --sat_fm_lemmas                         false
% 3.11/0.98  --sat_fm_prep                           false
% 3.11/0.98  --sat_fm_uc_incr                        true
% 3.11/0.98  --sat_out_model                         small
% 3.11/0.98  --sat_out_clauses                       false
% 3.11/0.98  
% 3.11/0.98  ------ QBF Options
% 3.11/0.98  
% 3.11/0.98  --qbf_mode                              false
% 3.11/0.98  --qbf_elim_univ                         false
% 3.11/0.98  --qbf_dom_inst                          none
% 3.11/0.98  --qbf_dom_pre_inst                      false
% 3.11/0.98  --qbf_sk_in                             false
% 3.11/0.98  --qbf_pred_elim                         true
% 3.11/0.98  --qbf_split                             512
% 3.11/0.98  
% 3.11/0.98  ------ BMC1 Options
% 3.11/0.98  
% 3.11/0.98  --bmc1_incremental                      false
% 3.11/0.98  --bmc1_axioms                           reachable_all
% 3.11/0.98  --bmc1_min_bound                        0
% 3.11/0.98  --bmc1_max_bound                        -1
% 3.11/0.98  --bmc1_max_bound_default                -1
% 3.11/0.98  --bmc1_symbol_reachability              true
% 3.11/0.98  --bmc1_property_lemmas                  false
% 3.11/0.98  --bmc1_k_induction                      false
% 3.11/0.98  --bmc1_non_equiv_states                 false
% 3.11/0.98  --bmc1_deadlock                         false
% 3.11/0.98  --bmc1_ucm                              false
% 3.11/0.98  --bmc1_add_unsat_core                   none
% 3.11/0.98  --bmc1_unsat_core_children              false
% 3.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.98  --bmc1_out_stat                         full
% 3.11/0.98  --bmc1_ground_init                      false
% 3.11/0.98  --bmc1_pre_inst_next_state              false
% 3.11/0.98  --bmc1_pre_inst_state                   false
% 3.11/0.98  --bmc1_pre_inst_reach_state             false
% 3.11/0.98  --bmc1_out_unsat_core                   false
% 3.11/0.98  --bmc1_aig_witness_out                  false
% 3.11/0.98  --bmc1_verbose                          false
% 3.11/0.98  --bmc1_dump_clauses_tptp                false
% 3.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.98  --bmc1_dump_file                        -
% 3.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.98  --bmc1_ucm_extend_mode                  1
% 3.11/0.98  --bmc1_ucm_init_mode                    2
% 3.11/0.98  --bmc1_ucm_cone_mode                    none
% 3.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.98  --bmc1_ucm_relax_model                  4
% 3.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.98  --bmc1_ucm_layered_model                none
% 3.11/0.98  --bmc1_ucm_max_lemma_size               10
% 3.11/0.98  
% 3.11/0.98  ------ AIG Options
% 3.11/0.98  
% 3.11/0.98  --aig_mode                              false
% 3.11/0.98  
% 3.11/0.98  ------ Instantiation Options
% 3.11/0.98  
% 3.11/0.98  --instantiation_flag                    true
% 3.11/0.98  --inst_sos_flag                         false
% 3.11/0.98  --inst_sos_phase                        true
% 3.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel_side                     none
% 3.11/0.98  --inst_solver_per_active                1400
% 3.11/0.98  --inst_solver_calls_frac                1.
% 3.11/0.98  --inst_passive_queue_type               priority_queues
% 3.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.98  --inst_passive_queues_freq              [25;2]
% 3.11/0.98  --inst_dismatching                      true
% 3.11/0.98  --inst_eager_unprocessed_to_passive     true
% 3.11/0.98  --inst_prop_sim_given                   true
% 3.11/0.98  --inst_prop_sim_new                     false
% 3.11/0.98  --inst_subs_new                         false
% 3.11/0.98  --inst_eq_res_simp                      false
% 3.11/0.98  --inst_subs_given                       false
% 3.11/0.98  --inst_orphan_elimination               true
% 3.11/0.98  --inst_learning_loop_flag               true
% 3.11/0.98  --inst_learning_start                   3000
% 3.11/0.98  --inst_learning_factor                  2
% 3.11/0.98  --inst_start_prop_sim_after_learn       3
% 3.11/0.98  --inst_sel_renew                        solver
% 3.11/0.98  --inst_lit_activity_flag                true
% 3.11/0.98  --inst_restr_to_given                   false
% 3.11/0.98  --inst_activity_threshold               500
% 3.11/0.98  --inst_out_proof                        true
% 3.11/0.98  
% 3.11/0.98  ------ Resolution Options
% 3.11/0.98  
% 3.11/0.98  --resolution_flag                       false
% 3.11/0.98  --res_lit_sel                           adaptive
% 3.11/0.98  --res_lit_sel_side                      none
% 3.11/0.98  --res_ordering                          kbo
% 3.11/0.98  --res_to_prop_solver                    active
% 3.11/0.98  --res_prop_simpl_new                    false
% 3.11/0.98  --res_prop_simpl_given                  true
% 3.11/0.98  --res_passive_queue_type                priority_queues
% 3.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.98  --res_passive_queues_freq               [15;5]
% 3.11/0.98  --res_forward_subs                      full
% 3.11/0.98  --res_backward_subs                     full
% 3.11/0.98  --res_forward_subs_resolution           true
% 3.11/0.98  --res_backward_subs_resolution          true
% 3.11/0.98  --res_orphan_elimination                true
% 3.11/0.98  --res_time_limit                        2.
% 3.11/0.98  --res_out_proof                         true
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Options
% 3.11/0.98  
% 3.11/0.98  --superposition_flag                    true
% 3.11/0.98  --sup_passive_queue_type                priority_queues
% 3.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.98  --demod_completeness_check              fast
% 3.11/0.98  --demod_use_ground                      true
% 3.11/0.98  --sup_to_prop_solver                    passive
% 3.11/0.98  --sup_prop_simpl_new                    true
% 3.11/0.98  --sup_prop_simpl_given                  true
% 3.11/0.98  --sup_fun_splitting                     false
% 3.11/0.98  --sup_smt_interval                      50000
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Simplification Setup
% 3.11/0.98  
% 3.11/0.98  --sup_indices_passive                   []
% 3.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_full_bw                           [BwDemod]
% 3.11/0.98  --sup_immed_triv                        [TrivRules]
% 3.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_immed_bw_main                     []
% 3.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.98  
% 3.11/0.98  ------ Combination Options
% 3.11/0.98  
% 3.11/0.98  --comb_res_mult                         3
% 3.11/0.98  --comb_sup_mult                         2
% 3.11/0.98  --comb_inst_mult                        10
% 3.11/0.98  
% 3.11/0.98  ------ Debug Options
% 3.11/0.98  
% 3.11/0.98  --dbg_backtrace                         false
% 3.11/0.98  --dbg_dump_prop_clauses                 false
% 3.11/0.98  --dbg_dump_prop_clauses_file            -
% 3.11/0.98  --dbg_out_stat                          false
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  ------ Proving...
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  % SZS status Theorem for theBenchmark.p
% 3.11/0.98  
% 3.11/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.98  
% 3.11/0.98  fof(f4,axiom,(
% 3.11/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f21,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.11/0.98    inference(ennf_transformation,[],[f4])).
% 3.11/0.98  
% 3.11/0.98  fof(f22,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.11/0.98    inference(flattening,[],[f21])).
% 3.11/0.98  
% 3.11/0.98  fof(f41,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.11/0.98    inference(nnf_transformation,[],[f22])).
% 3.11/0.98  
% 3.11/0.98  fof(f42,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.11/0.98    inference(rectify,[],[f41])).
% 3.11/0.98  
% 3.11/0.98  fof(f43,plain,(
% 3.11/0.98    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 3.11/0.98    introduced(choice_axiom,[])).
% 3.11/0.98  
% 3.11/0.98  fof(f44,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.11/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.11/0.98  
% 3.11/0.98  fof(f55,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f44])).
% 3.11/0.98  
% 3.11/0.98  fof(f14,conjecture,(
% 3.11/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f15,negated_conjecture,(
% 3.11/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 3.11/0.98    inference(negated_conjecture,[],[f14])).
% 3.11/0.98  
% 3.11/0.98  fof(f39,plain,(
% 3.11/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.11/0.98    inference(ennf_transformation,[],[f15])).
% 3.11/0.98  
% 3.11/0.98  fof(f40,plain,(
% 3.11/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.11/0.98    inference(flattening,[],[f39])).
% 3.11/0.98  
% 3.11/0.98  fof(f49,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK5) & ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.11/0.98    introduced(choice_axiom,[])).
% 3.11/0.98  
% 3.11/0.98  fof(f48,plain,(
% 3.11/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK4,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.11/0.98    introduced(choice_axiom,[])).
% 3.11/0.98  
% 3.11/0.98  fof(f47,plain,(
% 3.11/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK3),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.11/0.98    introduced(choice_axiom,[])).
% 3.11/0.98  
% 3.11/0.98  fof(f46,plain,(
% 3.11/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK2,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.11/0.98    introduced(choice_axiom,[])).
% 3.11/0.98  
% 3.11/0.98  fof(f45,plain,(
% 3.11/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X1,sK1,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK1),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.11/0.98    introduced(choice_axiom,[])).
% 3.11/0.98  
% 3.11/0.98  fof(f50,plain,(
% 3.11/0.98    ((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) & ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.11/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f49,f48,f47,f46,f45])).
% 3.11/0.98  
% 3.11/0.98  fof(f84,plain,(
% 3.11/0.98    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f80,plain,(
% 3.11/0.98    v1_funct_1(sK5)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f81,plain,(
% 3.11/0.98    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f82,plain,(
% 3.11/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f71,plain,(
% 3.11/0.98    l1_pre_topc(sK1)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f77,plain,(
% 3.11/0.98    v1_funct_1(sK4)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f78,plain,(
% 3.11/0.98    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f79,plain,(
% 3.11/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f8,axiom,(
% 3.11/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f29,plain,(
% 3.11/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.11/0.98    inference(ennf_transformation,[],[f8])).
% 3.11/0.98  
% 3.11/0.98  fof(f61,plain,(
% 3.11/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f29])).
% 3.11/0.98  
% 3.11/0.98  fof(f74,plain,(
% 3.11/0.98    l1_pre_topc(sK2)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f9,axiom,(
% 3.11/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f30,plain,(
% 3.11/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.11/0.98    inference(ennf_transformation,[],[f9])).
% 3.11/0.98  
% 3.11/0.98  fof(f62,plain,(
% 3.11/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f30])).
% 3.11/0.98  
% 3.11/0.98  fof(f76,plain,(
% 3.11/0.98    m1_pre_topc(sK3,sK2)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f13,axiom,(
% 3.11/0.98    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f37,plain,(
% 3.11/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.11/0.98    inference(ennf_transformation,[],[f13])).
% 3.11/0.98  
% 3.11/0.98  fof(f38,plain,(
% 3.11/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.11/0.98    inference(flattening,[],[f37])).
% 3.11/0.98  
% 3.11/0.98  fof(f66,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f38])).
% 3.11/0.98  
% 3.11/0.98  fof(f67,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f38])).
% 3.11/0.98  
% 3.11/0.98  fof(f68,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f38])).
% 3.11/0.98  
% 3.11/0.98  fof(f10,axiom,(
% 3.11/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f31,plain,(
% 3.11/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.11/0.98    inference(ennf_transformation,[],[f10])).
% 3.11/0.98  
% 3.11/0.98  fof(f32,plain,(
% 3.11/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.11/0.98    inference(flattening,[],[f31])).
% 3.11/0.98  
% 3.11/0.98  fof(f63,plain,(
% 3.11/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f32])).
% 3.11/0.98  
% 3.11/0.98  fof(f75,plain,(
% 3.11/0.98    ~v2_struct_0(sK3)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f11,axiom,(
% 3.11/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f33,plain,(
% 3.11/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.11/0.98    inference(ennf_transformation,[],[f11])).
% 3.11/0.98  
% 3.11/0.98  fof(f34,plain,(
% 3.11/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.11/0.98    inference(flattening,[],[f33])).
% 3.11/0.98  
% 3.11/0.98  fof(f64,plain,(
% 3.11/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f34])).
% 3.11/0.98  
% 3.11/0.98  fof(f72,plain,(
% 3.11/0.98    ~v2_struct_0(sK2)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f1,axiom,(
% 3.11/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f16,plain,(
% 3.11/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.11/0.98    inference(ennf_transformation,[],[f1])).
% 3.11/0.98  
% 3.11/0.98  fof(f17,plain,(
% 3.11/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.11/0.98    inference(flattening,[],[f16])).
% 3.11/0.98  
% 3.11/0.98  fof(f51,plain,(
% 3.11/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f17])).
% 3.11/0.98  
% 3.11/0.98  fof(f83,plain,(
% 3.11/0.98    ( ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f12,axiom,(
% 3.11/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f35,plain,(
% 3.11/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.11/0.98    inference(ennf_transformation,[],[f12])).
% 3.11/0.98  
% 3.11/0.98  fof(f36,plain,(
% 3.11/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.11/0.98    inference(flattening,[],[f35])).
% 3.11/0.98  
% 3.11/0.98  fof(f65,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f36])).
% 3.11/0.98  
% 3.11/0.98  fof(f73,plain,(
% 3.11/0.98    v2_pre_topc(sK2)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f70,plain,(
% 3.11/0.98    v2_pre_topc(sK1)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f69,plain,(
% 3.11/0.98    ~v2_struct_0(sK1)),
% 3.11/0.98    inference(cnf_transformation,[],[f50])).
% 3.11/0.98  
% 3.11/0.98  fof(f6,axiom,(
% 3.11/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f25,plain,(
% 3.11/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.11/0.98    inference(ennf_transformation,[],[f6])).
% 3.11/0.98  
% 3.11/0.98  fof(f26,plain,(
% 3.11/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.11/0.98    inference(flattening,[],[f25])).
% 3.11/0.98  
% 3.11/0.98  fof(f59,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f26])).
% 3.11/0.98  
% 3.11/0.98  fof(f7,axiom,(
% 3.11/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f27,plain,(
% 3.11/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.11/0.98    inference(ennf_transformation,[],[f7])).
% 3.11/0.98  
% 3.11/0.98  fof(f28,plain,(
% 3.11/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.11/0.98    inference(flattening,[],[f27])).
% 3.11/0.98  
% 3.11/0.98  fof(f60,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f28])).
% 3.11/0.98  
% 3.11/0.98  fof(f56,plain,(
% 3.11/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f44])).
% 3.11/0.98  
% 3.11/0.98  fof(f2,axiom,(
% 3.11/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f18,plain,(
% 3.11/0.98    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.11/0.98    inference(ennf_transformation,[],[f2])).
% 3.11/0.98  
% 3.11/0.98  fof(f19,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.11/0.98    inference(flattening,[],[f18])).
% 3.11/0.98  
% 3.11/0.98  fof(f52,plain,(
% 3.11/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.11/0.98    inference(cnf_transformation,[],[f19])).
% 3.11/0.98  
% 3.11/0.98  fof(f3,axiom,(
% 3.11/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.11/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.98  
% 3.11/0.98  fof(f20,plain,(
% 3.11/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.98    inference(ennf_transformation,[],[f3])).
% 3.11/0.98  
% 3.11/0.98  fof(f53,plain,(
% 3.11/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.98    inference(cnf_transformation,[],[f20])).
% 3.11/0.98  
% 3.11/0.98  cnf(c_4,plain,
% 3.11/0.98      ( r2_funct_2(X0,X1,X2,X3)
% 3.11/0.98      | ~ v1_funct_2(X3,X0,X1)
% 3.11/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.11/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/0.98      | m1_subset_1(sK0(X0,X2,X3),X0)
% 3.11/0.98      | ~ v1_funct_1(X2)
% 3.11/0.98      | ~ v1_funct_1(X3) ),
% 3.11/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_18,negated_conjecture,
% 3.11/0.98      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
% 3.11/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_874,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/0.98      | ~ v1_funct_2(X3,X1,X2)
% 3.11/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | m1_subset_1(sK0(X1,X3,X0),X1)
% 3.11/0.98      | ~ v1_funct_1(X3)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
% 3.11/0.98      | u1_struct_0(sK1) != X2
% 3.11/0.98      | u1_struct_0(sK3) != X1
% 3.11/0.98      | sK5 != X0 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_875,plain,
% 3.11/0.98      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 3.11/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | ~ v1_funct_1(sK5) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_874]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_22,negated_conjecture,
% 3.11/0.98      ( v1_funct_1(sK5) ),
% 3.11/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_21,negated_conjecture,
% 3.11/0.98      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.11/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_20,negated_conjecture,
% 3.11/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.11/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_877,plain,
% 3.11/0.98      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_875,c_22,c_21,c_20]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_878,plain,
% 3.11/0.98      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 3.11/0.98      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
% 3.11/0.98      inference(renaming,[status(thm)],[c_877]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1294,plain,
% 3.11/0.98      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 3.11/0.98      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_878]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1852,plain,
% 3.11/0.98      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
% 3.11/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_31,negated_conjecture,
% 3.11/0.98      ( l1_pre_topc(sK1) ),
% 3.11/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_36,plain,
% 3.11/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_25,negated_conjecture,
% 3.11/0.98      ( v1_funct_1(sK4) ),
% 3.11/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_42,plain,
% 3.11/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_24,negated_conjecture,
% 3.11/0.98      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 3.11/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_43,plain,
% 3.11/0.98      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_23,negated_conjecture,
% 3.11/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.11/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_44,plain,
% 3.11/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_10,plain,
% 3.11/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_69,plain,
% 3.11/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_71,plain,
% 3.11/0.98      ( l1_pre_topc(sK1) != iProver_top
% 3.11/0.98      | l1_struct_0(sK1) = iProver_top ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_69]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_28,negated_conjecture,
% 3.11/0.98      ( l1_pre_topc(sK2) ),
% 3.11/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_596,plain,
% 3.11/0.98      ( l1_struct_0(X0) | sK2 != X0 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_597,plain,
% 3.11/0.98      ( l1_struct_0(sK2) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_596]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_598,plain,
% 3.11/0.98      ( l1_struct_0(sK2) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_11,plain,
% 3.11/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_26,negated_conjecture,
% 3.11/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.11/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_477,plain,
% 3.11/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK3 != X1 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_478,plain,
% 3.11/0.98      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_477]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_480,plain,
% 3.11/0.98      ( l1_pre_topc(sK3) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_478,c_28]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_610,plain,
% 3.11/0.98      ( l1_struct_0(X0) | sK3 != X0 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_480]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_611,plain,
% 3.11/0.98      ( l1_struct_0(sK3) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_610]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_612,plain,
% 3.11/0.98      ( l1_struct_0(sK3) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_879,plain,
% 3.11/0.98      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
% 3.11/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_17,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.98      | ~ l1_struct_0(X1)
% 3.11/0.98      | ~ l1_struct_0(X3)
% 3.11/0.98      | ~ l1_struct_0(X2)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 3.11/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1314,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.11/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.11/0.98      | ~ l1_struct_0(X1_56)
% 3.11/0.98      | ~ l1_struct_0(X2_56)
% 3.11/0.98      | ~ l1_struct_0(X0_56)
% 3.11/0.98      | ~ v1_funct_1(X0_54)
% 3.11/0.98      | v1_funct_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56)) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2175,plain,
% 3.11/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ l1_struct_0(X0_56)
% 3.11/0.98      | ~ l1_struct_0(sK2)
% 3.11/0.98      | ~ l1_struct_0(sK1)
% 3.11/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,X0_56))
% 3.11/0.98      | ~ v1_funct_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_1314]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2385,plain,
% 3.11/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ l1_struct_0(sK2)
% 3.11/0.98      | ~ l1_struct_0(sK1)
% 3.11/0.98      | ~ l1_struct_0(sK3)
% 3.11/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | ~ v1_funct_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_2175]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2386,plain,
% 3.11/0.98      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | l1_struct_0(sK2) != iProver_top
% 3.11/0.98      | l1_struct_0(sK1) != iProver_top
% 3.11/0.98      | l1_struct_0(sK3) != iProver_top
% 3.11/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_2385]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_16,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.98      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.98      | ~ l1_struct_0(X1)
% 3.11/0.98      | ~ l1_struct_0(X3)
% 3.11/0.98      | ~ l1_struct_0(X2)
% 3.11/0.98      | ~ v1_funct_1(X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1315,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.11/0.98      | v1_funct_2(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),u1_struct_0(X2_56),u1_struct_0(X1_56))
% 3.11/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.11/0.98      | ~ l1_struct_0(X1_56)
% 3.11/0.98      | ~ l1_struct_0(X2_56)
% 3.11/0.98      | ~ l1_struct_0(X0_56)
% 3.11/0.98      | ~ v1_funct_1(X0_54) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2185,plain,
% 3.11/0.98      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,X0_56),u1_struct_0(X0_56),u1_struct_0(sK1))
% 3.11/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ l1_struct_0(X0_56)
% 3.11/0.98      | ~ l1_struct_0(sK2)
% 3.11/0.98      | ~ l1_struct_0(sK1)
% 3.11/0.98      | ~ v1_funct_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_1315]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2768,plain,
% 3.11/0.98      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ l1_struct_0(sK2)
% 3.11/0.98      | ~ l1_struct_0(sK1)
% 3.11/0.98      | ~ l1_struct_0(sK3)
% 3.11/0.98      | ~ v1_funct_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_2185]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2769,plain,
% 3.11/0.98      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 3.11/0.98      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | l1_struct_0(sK2) != iProver_top
% 3.11/0.98      | l1_struct_0(sK1) != iProver_top
% 3.11/0.98      | l1_struct_0(sK3) != iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_2768]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_15,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.98      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.11/0.98      | ~ l1_struct_0(X1)
% 3.11/0.98      | ~ l1_struct_0(X3)
% 3.11/0.98      | ~ l1_struct_0(X2)
% 3.11/0.98      | ~ v1_funct_1(X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1316,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.11/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.11/0.98      | m1_subset_1(k2_tmap_1(X0_56,X1_56,X0_54,X2_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 3.11/0.98      | ~ l1_struct_0(X1_56)
% 3.11/0.98      | ~ l1_struct_0(X2_56)
% 3.11/0.98      | ~ l1_struct_0(X0_56)
% 3.11/0.98      | ~ v1_funct_1(X0_54) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2195,plain,
% 3.11/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1))))
% 3.11/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ l1_struct_0(X0_56)
% 3.11/0.98      | ~ l1_struct_0(sK2)
% 3.11/0.98      | ~ l1_struct_0(sK1)
% 3.11/0.98      | ~ v1_funct_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_1316]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3072,plain,
% 3.11/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ l1_struct_0(sK2)
% 3.11/0.98      | ~ l1_struct_0(sK1)
% 3.11/0.98      | ~ l1_struct_0(sK3)
% 3.11/0.98      | ~ v1_funct_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_2195]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3073,plain,
% 3.11/0.98      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 3.11/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | l1_struct_0(sK2) != iProver_top
% 3.11/0.98      | l1_struct_0(sK1) != iProver_top
% 3.11/0.98      | l1_struct_0(sK3) != iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_3072]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3569,plain,
% 3.11/0.98      ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_1852,c_36,c_42,c_43,c_44,c_71,c_598,c_612,c_879,
% 3.11/0.98                 c_2386,c_2769,c_3073]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_12,plain,
% 3.11/0.98      ( v2_struct_0(X0)
% 3.11/0.98      | ~ l1_struct_0(X0)
% 3.11/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.11/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_27,negated_conjecture,
% 3.11/0.98      ( ~ v2_struct_0(sK3) ),
% 3.11/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_623,plain,
% 3.11/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_624,plain,
% 3.11/0.98      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_623]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_626,plain,
% 3.11/0.98      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_624,c_611]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_13,plain,
% 3.11/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.11/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.11/0.98      | m1_subset_1(X2,u1_struct_0(X1))
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | v2_struct_0(X0)
% 3.11/0.98      | ~ l1_pre_topc(X1) ),
% 3.11/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_459,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.11/0.98      | m1_subset_1(X0,u1_struct_0(X2))
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | v2_struct_0(X2)
% 3.11/0.98      | ~ l1_pre_topc(X2)
% 3.11/0.98      | sK2 != X2
% 3.11/0.98      | sK3 != X1 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_460,plain,
% 3.11/0.98      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.11/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.11/0.98      | v2_struct_0(sK2)
% 3.11/0.98      | v2_struct_0(sK3)
% 3.11/0.98      | ~ l1_pre_topc(sK2) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_459]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_30,negated_conjecture,
% 3.11/0.98      ( ~ v2_struct_0(sK2) ),
% 3.11/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_464,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.11/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_460,c_30,c_28,c_27]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_465,plain,
% 3.11/0.98      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.11/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.11/0.98      inference(renaming,[status(thm)],[c_464]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_0,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.11/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_19,negated_conjecture,
% 3.11/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.11/0.98      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.11/0.98      | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_404,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,X1)
% 3.11/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.11/0.98      | v1_xboole_0(X1)
% 3.11/0.98      | X2 != X0
% 3.11/0.98      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X2) = k1_funct_1(sK5,X2)
% 3.11/0.98      | u1_struct_0(sK3) != X1 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_405,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.11/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.11/0.98      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_404]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_522,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 3.11/0.98      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.11/0.98      inference(backward_subsumption_resolution,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_465,c_405]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_657,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.11/0.98      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.11/0.98      inference(backward_subsumption_resolution,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_626,c_522]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1297,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 3.11/0.98      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_657]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1849,plain,
% 3.11/0.98      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK5,X0_54)
% 3.11/0.98      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_4715,plain,
% 3.11/0.98      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_3569,c_1849]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1310,negated_conjecture,
% 3.11/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1836,plain,
% 3.11/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_14,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.98      | ~ m1_pre_topc(X3,X1)
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.98      | ~ v2_pre_topc(X2)
% 3.11/0.98      | ~ v2_pre_topc(X1)
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | v2_struct_0(X2)
% 3.11/0.98      | ~ l1_pre_topc(X1)
% 3.11/0.98      | ~ l1_pre_topc(X2)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.11/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_488,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/0.98      | ~ v2_pre_topc(X1)
% 3.11/0.98      | ~ v2_pre_topc(X2)
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | v2_struct_0(X2)
% 3.11/0.98      | ~ l1_pre_topc(X1)
% 3.11/0.98      | ~ l1_pre_topc(X2)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.11/0.98      | sK2 != X1
% 3.11/0.98      | sK3 != X3 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_489,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.11/0.98      | ~ v2_pre_topc(X1)
% 3.11/0.98      | ~ v2_pre_topc(sK2)
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | v2_struct_0(sK2)
% 3.11/0.98      | ~ l1_pre_topc(X1)
% 3.11/0.98      | ~ l1_pre_topc(sK2)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_29,negated_conjecture,
% 3.11/0.98      ( v2_pre_topc(sK2) ),
% 3.11/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_493,plain,
% 3.11/0.98      ( ~ l1_pre_topc(X1)
% 3.11/0.98      | ~ v2_pre_topc(X1)
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.11/0.98      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_489,c_30,c_29,c_28]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_494,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.11/0.98      | ~ v2_pre_topc(X1)
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | ~ l1_pre_topc(X1)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 3.11/0.98      inference(renaming,[status(thm)],[c_493]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_32,negated_conjecture,
% 3.11/0.98      ( v2_pre_topc(sK1) ),
% 3.11/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_562,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 3.11/0.98      | v2_struct_0(X1)
% 3.11/0.98      | ~ l1_pre_topc(X1)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
% 3.11/0.98      | sK1 != X1 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_494,c_32]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_563,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | v2_struct_0(sK1)
% 3.11/0.98      | ~ l1_pre_topc(sK1)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_562]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_33,negated_conjecture,
% 3.11/0.98      ( ~ v2_struct_0(sK1) ),
% 3.11/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_567,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_563,c_33,c_31]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1304,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(X0_54)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_567]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1842,plain,
% 3.11/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3)
% 3.11/0.98      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | v1_funct_1(X0_54) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3381,plain,
% 3.11/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 3.11/0.98      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_1836,c_1842]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_8,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.11/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1318,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.11/0.98      | ~ v1_funct_1(X0_54)
% 3.11/0.98      | k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1828,plain,
% 3.11/0.98      ( k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55)
% 3.11/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.11/0.98      | v1_funct_1(X0_54) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2503,plain,
% 3.11/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55)
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_1836,c_1828]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2155,plain,
% 3.11/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(sK4)
% 3.11/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_1318]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3292,plain,
% 3.11/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_2503,c_25,c_23,c_2155]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3415,plain,
% 3.11/0.98      ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
% 3.11/0.98      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.98      inference(demodulation,[status(thm)],[c_3381,c_3292]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5016,plain,
% 3.11/0.98      ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_3415,c_42,c_43]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1306,plain,
% 3.11/0.98      ( m1_subset_1(X0_54,u1_struct_0(sK2))
% 3.11/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_465]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1840,plain,
% 3.11/0.98      ( m1_subset_1(X0_54,u1_struct_0(sK2)) = iProver_top
% 3.11/0.98      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1306]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3574,plain,
% 3.11/0.98      ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK2)) = iProver_top ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_3569,c_1840]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_9,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/0.98      | ~ m1_subset_1(X3,X1)
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | v1_xboole_0(X1)
% 3.11/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.11/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1317,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.11/0.98      | ~ m1_subset_1(X1_54,X0_55)
% 3.11/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.11/0.98      | ~ v1_funct_1(X0_54)
% 3.11/0.98      | v1_xboole_0(X0_55)
% 3.11/0.98      | k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1829,plain,
% 3.11/0.98      ( k3_funct_2(X0_55,X1_55,X0_54,X1_54) = k1_funct_1(X0_54,X1_54)
% 3.11/0.98      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.11/0.98      | m1_subset_1(X1_54,X0_55) != iProver_top
% 3.11/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.11/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.11/0.98      | v1_xboole_0(X0_55) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2616,plain,
% 3.11/0.98      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
% 3.11/0.98      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_1836,c_1829]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_634,plain,
% 3.11/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_635,plain,
% 3.11/0.98      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_634]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_636,plain,
% 3.11/0.98      ( l1_struct_0(sK2) != iProver_top
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3711,plain,
% 3.11/0.98      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
% 3.11/0.98      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_2616,c_42,c_43,c_598,c_636]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_4574,plain,
% 3.11/0.98      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_3574,c_3711]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5205,plain,
% 3.11/0.98      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.11/0.98      inference(light_normalisation,[status(thm)],[c_4574,c_5016]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5286,plain,
% 3.11/0.98      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.11/0.98      inference(light_normalisation,[status(thm)],[c_4715,c_5016,c_5205]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3,plain,
% 3.11/0.98      ( r2_funct_2(X0,X1,X2,X3)
% 3.11/0.98      | ~ v1_funct_2(X3,X0,X1)
% 3.11/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.11/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/0.98      | ~ v1_funct_1(X2)
% 3.11/0.98      | ~ v1_funct_1(X3)
% 3.11/0.98      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 3.11/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_894,plain,
% 3.11/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/0.98      | ~ v1_funct_2(X3,X1,X2)
% 3.11/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | ~ v1_funct_1(X3)
% 3.11/0.98      | ~ v1_funct_1(X0)
% 3.11/0.98      | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
% 3.11/0.98      | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
% 3.11/0.98      | u1_struct_0(sK1) != X2
% 3.11/0.98      | u1_struct_0(sK3) != X1
% 3.11/0.98      | sK5 != X0 ),
% 3.11/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_895,plain,
% 3.11/0.98      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | ~ v1_funct_1(sK5)
% 3.11/0.98      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(unflattening,[status(thm)],[c_894]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_897,plain,
% 3.11/0.98      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_895,c_22,c_21,c_20]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_898,plain,
% 3.11/0.98      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(renaming,[status(thm)],[c_897]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1293,plain,
% 3.11/0.98      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.11/0.98      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.11/0.98      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 3.11/0.98      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_898]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1853,plain,
% 3.11/0.98      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5))
% 3.11/0.98      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.11/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_70,plain,
% 3.11/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_3577,plain,
% 3.11/0.98      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 3.11/0.98      inference(global_propositional_subsumption,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_1853,c_31,c_25,c_24,c_23,c_70,c_597,c_611,c_1293,
% 3.11/0.98                 c_2385,c_2768,c_3072]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5020,plain,
% 3.11/0.98      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.11/0.98      inference(demodulation,[status(thm)],[c_5016,c_3577]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5289,plain,
% 3.11/0.98      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 3.11/0.98      inference(demodulation,[status(thm)],[c_5286,c_5020]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5021,plain,
% 3.11/0.98      ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.11/0.98      inference(demodulation,[status(thm)],[c_5016,c_3569]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1,plain,
% 3.11/0.98      ( ~ r2_hidden(X0,X1)
% 3.11/0.98      | ~ v1_relat_1(X2)
% 3.11/0.98      | ~ v1_funct_1(X2)
% 3.11/0.98      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_384,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,X1)
% 3.11/0.98      | ~ v1_relat_1(X2)
% 3.11/0.98      | ~ v1_funct_1(X2)
% 3.11/0.98      | v1_xboole_0(X1)
% 3.11/0.98      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 3.11/0.98      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1307,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0_54,X0_55)
% 3.11/0.98      | ~ v1_relat_1(X1_54)
% 3.11/0.98      | ~ v1_funct_1(X1_54)
% 3.11/0.98      | v1_xboole_0(X0_55)
% 3.11/0.98      | k1_funct_1(k7_relat_1(X1_54,X0_55),X0_54) = k1_funct_1(X1_54,X0_54) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_384]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1839,plain,
% 3.11/0.98      ( k1_funct_1(k7_relat_1(X0_54,X0_55),X1_54) = k1_funct_1(X0_54,X1_54)
% 3.11/0.98      | m1_subset_1(X1_54,X0_55) != iProver_top
% 3.11/0.98      | v1_relat_1(X0_54) != iProver_top
% 3.11/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.11/0.98      | v1_xboole_0(X0_55) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5103,plain,
% 3.11/0.98      ( k1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(X0_54,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 3.11/0.98      | v1_relat_1(X0_54) != iProver_top
% 3.11/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.11/0.98      inference(superposition,[status(thm)],[c_5021,c_1839]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_5117,plain,
% 3.11/0.98      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 3.11/0.98      | v1_relat_1(sK4) != iProver_top
% 3.11/0.98      | v1_funct_1(sK4) != iProver_top
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_5103]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.98      | v1_relat_1(X0) ),
% 3.11/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_1321,plain,
% 3.11/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.11/0.98      | v1_relat_1(X0_54) ),
% 3.11/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2112,plain,
% 3.11/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.11/0.98      | v1_relat_1(sK4) ),
% 3.11/0.98      inference(instantiation,[status(thm)],[c_1321]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_2113,plain,
% 3.11/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.11/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(c_625,plain,
% 3.11/0.98      ( l1_struct_0(sK3) != iProver_top
% 3.11/0.98      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.11/0.98      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 3.11/0.98  
% 3.11/0.98  cnf(contradiction,plain,
% 3.11/0.98      ( $false ),
% 3.11/0.98      inference(minisat,
% 3.11/0.98                [status(thm)],
% 3.11/0.98                [c_5289,c_5117,c_2113,c_625,c_612,c_44,c_42]) ).
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/0.98  
% 3.11/0.98  ------                               Statistics
% 3.11/0.98  
% 3.11/0.98  ------ General
% 3.11/0.98  
% 3.11/0.98  abstr_ref_over_cycles:                  0
% 3.11/0.98  abstr_ref_under_cycles:                 0
% 3.11/0.98  gc_basic_clause_elim:                   0
% 3.11/0.98  forced_gc_time:                         0
% 3.11/0.98  parsing_time:                           0.012
% 3.11/0.98  unif_index_cands_time:                  0.
% 3.11/0.98  unif_index_add_time:                    0.
% 3.11/0.98  orderings_time:                         0.
% 3.11/0.98  out_proof_time:                         0.014
% 3.11/0.98  total_time:                             0.204
% 3.11/0.98  num_of_symbols:                         59
% 3.11/0.98  num_of_terms:                           5773
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing
% 3.11/0.98  
% 3.11/0.98  num_of_splits:                          0
% 3.11/0.98  num_of_split_atoms:                     0
% 3.11/0.98  num_of_reused_defs:                     0
% 3.11/0.98  num_eq_ax_congr_red:                    38
% 3.11/0.98  num_of_sem_filtered_clauses:            1
% 3.11/0.98  num_of_subtypes:                        5
% 3.11/0.98  monotx_restored_types:                  0
% 3.11/0.98  sat_num_of_epr_types:                   0
% 3.11/0.98  sat_num_of_non_cyclic_types:            0
% 3.11/0.98  sat_guarded_non_collapsed_types:        0
% 3.11/0.98  num_pure_diseq_elim:                    0
% 3.11/0.98  simp_replaced_by:                       0
% 3.11/0.98  res_preprocessed:                       144
% 3.11/0.98  prep_upred:                             0
% 3.11/0.98  prep_unflattend:                        39
% 3.11/0.98  smt_new_axioms:                         0
% 3.11/0.98  pred_elim_cands:                        6
% 3.11/0.98  pred_elim:                              6
% 3.11/0.98  pred_elim_cl:                           5
% 3.11/0.98  pred_elim_cycles:                       12
% 3.11/0.98  merged_defs:                            0
% 3.11/0.98  merged_defs_ncl:                        0
% 3.11/0.98  bin_hyper_res:                          0
% 3.11/0.98  prep_cycles:                            4
% 3.11/0.98  pred_elim_time:                         0.019
% 3.11/0.98  splitting_time:                         0.
% 3.11/0.98  sem_filter_time:                        0.
% 3.11/0.98  monotx_time:                            0.
% 3.11/0.98  subtype_inf_time:                       0.
% 3.11/0.98  
% 3.11/0.98  ------ Problem properties
% 3.11/0.98  
% 3.11/0.98  clauses:                                29
% 3.11/0.98  conjectures:                            6
% 3.11/0.98  epr:                                    5
% 3.11/0.98  horn:                                   26
% 3.11/0.98  ground:                                 14
% 3.11/0.98  unary:                                  12
% 3.11/0.98  binary:                                 3
% 3.11/0.98  lits:                                   93
% 3.11/0.98  lits_eq:                                10
% 3.11/0.98  fd_pure:                                0
% 3.11/0.98  fd_pseudo:                              0
% 3.11/0.98  fd_cond:                                0
% 3.11/0.98  fd_pseudo_cond:                         0
% 3.11/0.98  ac_symbols:                             0
% 3.11/0.98  
% 3.11/0.98  ------ Propositional Solver
% 3.11/0.98  
% 3.11/0.98  prop_solver_calls:                      28
% 3.11/0.98  prop_fast_solver_calls:                 1241
% 3.11/0.98  smt_solver_calls:                       0
% 3.11/0.98  smt_fast_solver_calls:                  0
% 3.11/0.98  prop_num_of_clauses:                    1959
% 3.11/0.98  prop_preprocess_simplified:             5756
% 3.11/0.98  prop_fo_subsumed:                       55
% 3.11/0.98  prop_solver_time:                       0.
% 3.11/0.99  smt_solver_time:                        0.
% 3.11/0.99  smt_fast_solver_time:                   0.
% 3.11/0.99  prop_fast_solver_time:                  0.
% 3.11/0.99  prop_unsat_core_time:                   0.
% 3.11/0.99  
% 3.11/0.99  ------ QBF
% 3.11/0.99  
% 3.11/0.99  qbf_q_res:                              0
% 3.11/0.99  qbf_num_tautologies:                    0
% 3.11/0.99  qbf_prep_cycles:                        0
% 3.11/0.99  
% 3.11/0.99  ------ BMC1
% 3.11/0.99  
% 3.11/0.99  bmc1_current_bound:                     -1
% 3.11/0.99  bmc1_last_solved_bound:                 -1
% 3.11/0.99  bmc1_unsat_core_size:                   -1
% 3.11/0.99  bmc1_unsat_core_parents_size:           -1
% 3.11/0.99  bmc1_merge_next_fun:                    0
% 3.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation
% 3.11/0.99  
% 3.11/0.99  inst_num_of_clauses:                    491
% 3.11/0.99  inst_num_in_passive:                    78
% 3.11/0.99  inst_num_in_active:                     275
% 3.11/0.99  inst_num_in_unprocessed:                139
% 3.11/0.99  inst_num_of_loops:                      290
% 3.11/0.99  inst_num_of_learning_restarts:          0
% 3.11/0.99  inst_num_moves_active_passive:          11
% 3.11/0.99  inst_lit_activity:                      0
% 3.11/0.99  inst_lit_activity_moves:                0
% 3.11/0.99  inst_num_tautologies:                   0
% 3.11/0.99  inst_num_prop_implied:                  0
% 3.11/0.99  inst_num_existing_simplified:           0
% 3.11/0.99  inst_num_eq_res_simplified:             0
% 3.11/0.99  inst_num_child_elim:                    0
% 3.11/0.99  inst_num_of_dismatching_blockings:      72
% 3.11/0.99  inst_num_of_non_proper_insts:           313
% 3.11/0.99  inst_num_of_duplicates:                 0
% 3.11/0.99  inst_inst_num_from_inst_to_res:         0
% 3.11/0.99  inst_dismatching_checking_time:         0.
% 3.11/0.99  
% 3.11/0.99  ------ Resolution
% 3.11/0.99  
% 3.11/0.99  res_num_of_clauses:                     0
% 3.11/0.99  res_num_in_passive:                     0
% 3.11/0.99  res_num_in_active:                      0
% 3.11/0.99  res_num_of_loops:                       148
% 3.11/0.99  res_forward_subset_subsumed:            18
% 3.11/0.99  res_backward_subset_subsumed:           4
% 3.11/0.99  res_forward_subsumed:                   0
% 3.11/0.99  res_backward_subsumed:                  0
% 3.11/0.99  res_forward_subsumption_resolution:     0
% 3.11/0.99  res_backward_subsumption_resolution:    2
% 3.11/0.99  res_clause_to_clause_subsumption:       168
% 3.11/0.99  res_orphan_elimination:                 0
% 3.11/0.99  res_tautology_del:                      49
% 3.11/0.99  res_num_eq_res_simplified:              0
% 3.11/0.99  res_num_sel_changes:                    0
% 3.11/0.99  res_moves_from_active_to_pass:          0
% 3.11/0.99  
% 3.11/0.99  ------ Superposition
% 3.11/0.99  
% 3.11/0.99  sup_time_total:                         0.
% 3.11/0.99  sup_time_generating:                    0.
% 3.11/0.99  sup_time_sim_full:                      0.
% 3.11/0.99  sup_time_sim_immed:                     0.
% 3.11/0.99  
% 3.11/0.99  sup_num_of_clauses:                     98
% 3.11/0.99  sup_num_in_active:                      47
% 3.11/0.99  sup_num_in_passive:                     51
% 3.11/0.99  sup_num_of_loops:                       56
% 3.11/0.99  sup_fw_superposition:                   35
% 3.11/0.99  sup_bw_superposition:                   38
% 3.11/0.99  sup_immediate_simplified:               5
% 3.11/0.99  sup_given_eliminated:                   0
% 3.11/0.99  comparisons_done:                       0
% 3.11/0.99  comparisons_avoided:                    0
% 3.11/0.99  
% 3.11/0.99  ------ Simplifications
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  sim_fw_subset_subsumed:                 0
% 3.11/0.99  sim_bw_subset_subsumed:                 1
% 3.11/0.99  sim_fw_subsumed:                        1
% 3.11/0.99  sim_bw_subsumed:                        0
% 3.11/0.99  sim_fw_subsumption_res:                 1
% 3.11/0.99  sim_bw_subsumption_res:                 0
% 3.11/0.99  sim_tautology_del:                      0
% 3.11/0.99  sim_eq_tautology_del:                   1
% 3.11/0.99  sim_eq_res_simp:                        0
% 3.11/0.99  sim_fw_demodulated:                     1
% 3.11/0.99  sim_bw_demodulated:                     9
% 3.11/0.99  sim_light_normalised:                   5
% 3.11/0.99  sim_joinable_taut:                      0
% 3.11/0.99  sim_joinable_simp:                      0
% 3.11/0.99  sim_ac_normalised:                      0
% 3.11/0.99  sim_smt_subsumption:                    0
% 3.11/0.99  
%------------------------------------------------------------------------------
