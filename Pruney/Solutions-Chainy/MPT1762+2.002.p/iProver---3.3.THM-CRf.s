%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:50 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  164 (1891 expanded)
%              Number of clauses        :  111 ( 385 expanded)
%              Number of leaves         :   14 ( 856 expanded)
%              Depth                    :   20
%              Number of atoms          : 1356 (34892 expanded)
%              Number of equality atoms :  372 (2701 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal clause size      :   42 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
                        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
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
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f17])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & ! [X6] :
              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
              | ~ r2_hidden(X6,u1_struct_0(X2))
              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & ! [X6] :
            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(sK6,X6)
            | ~ r2_hidden(X6,u1_struct_0(X2))
            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & ! [X6] :
                  ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                  | ~ r2_hidden(X6,u1_struct_0(X2))
                  | ~ m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK5),X5)
            & ! [X6] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X6) = k1_funct_1(X5,X6)
                | ~ r2_hidden(X6,u1_struct_0(X2))
                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & ! [X6] :
                      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                      | ~ r2_hidden(X6,u1_struct_0(X2))
                      | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X4),X5)
                & ! [X6] :
                    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                    | ~ r2_hidden(X6,u1_struct_0(X2))
                    | ~ m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & ! [X6] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                          | ~ r2_hidden(X6,u1_struct_0(X2))
                          | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X2,X3)
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
                    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X4),X5)
                    & ! [X6] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                        | ~ r2_hidden(X6,u1_struct_0(sK3))
                        | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X4),X5)
                        & ! [X6] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X6) = k1_funct_1(X5,X6)
                            | ~ r2_hidden(X6,u1_struct_0(X2))
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X2,X3)
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

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & ! [X6] :
                                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                                | ~ r2_hidden(X6,u1_struct_0(X2))
                                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X2,X3)
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
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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

fof(f27,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)
    & ! [X6] :
        ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) = k1_funct_1(sK6,X6)
        | ~ r2_hidden(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(sK4)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK3,sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f18,f26,f25,f24,f23,f22,f21])).

fof(f53,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
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
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X6] :
      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) = k1_funct_1(sK6,X6)
      | ~ r2_hidden(X6,u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_388,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X4,X1,X3,X0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X4,X2,X3,X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_389,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_393,plain,
    ( ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | r2_hidden(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X3))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_11])).

cnf(c_394,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_1785,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | r2_hidden(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X2_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK2)
    | u1_struct_0(X2_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_2260,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK2)
    | u1_struct_0(X2_54) != u1_struct_0(sK3)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | r2_hidden(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X2_54)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1794,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2251,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1799,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2246,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1805,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2240,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_3067,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK2,sK4,X0_54,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2246,c_2240])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_30,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_36,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_37,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3590,plain,
    ( v2_pre_topc(X1_54) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK2,sK4,X0_54,sK5)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3067,c_29,c_30,c_31,c_36,c_37])).

cnf(c_3591,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK2,sK4,X0_54,sK5)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3590])).

cnf(c_3605,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK1,sK2,sK4,sK3,sK5)
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_3591])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1800,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2245,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1806,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2239,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1806])).

cnf(c_3005,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK2,sK5,X0_54)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2246,c_2239])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_27,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_34,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_35,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1796,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2249,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1796])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1808,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2237,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_2642,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_2237])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1807,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2621,plain,
    ( ~ m1_pre_topc(sK4,X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_2770,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_2771,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_3223,plain,
    ( m1_pre_topc(X0_54,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK2,sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_27,c_28,c_29,c_30,c_31,c_34,c_35,c_36,c_37,c_2642,c_2771])).

cnf(c_3224,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK2,sK5,X0_54)
    | m1_pre_topc(X0_54,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3223])).

cnf(c_3231,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_2245,c_3224])).

cnf(c_3612,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3605,c_3231])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3722,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3612,c_26,c_27,c_28,c_35,c_39])).

cnf(c_3730,plain,
    ( k2_tmap_1(X0_54,X1_54,X0_52,X2_54) != k2_tmap_1(sK4,sK2,sK5,sK3)
    | u1_struct_0(X1_54) != u1_struct_0(sK2)
    | u1_struct_0(X2_54) != u1_struct_0(sK3)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | r2_hidden(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X2_54)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2260,c_3722])).

cnf(c_3751,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3730])).

cnf(c_4020,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3751])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_41,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1810,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2527,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_2665,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_2530,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(X1_54),u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0_54,X1_54,X0_52,sK6),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK2))))
    | ~ m1_pre_topc(X1_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,X1_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2686,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0_54,sK3,X0_52,sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_2741,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK4,sK3,X0_52,sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,X0_52,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2686])).

cnf(c_2742,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,X0_52,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK3,X0_52,sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2741])).

cnf(c_2744,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,sK5,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_4022,plain,
    ( r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4020,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_34,c_35,c_36,c_37,c_38,c_39,c_41,c_42,c_2527,c_2642,c_2665,c_2744,c_2771,c_3612])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1804,negated_conjecture,
    ( ~ r2_hidden(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_52) = k1_funct_1(sK6,X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2241,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_52) = k1_funct_1(sK6,X0_52)
    | r2_hidden(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_4027,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(sK2,sK4,sK3,sK5,sK6)) = k1_funct_1(sK6,sK0(sK2,sK4,sK3,sK5,sK6))
    | m1_subset_1(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_2241])).

cnf(c_6,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_325,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X4,X1,X3,X0),u1_struct_0(X4))
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X4,X2,X3,X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_326,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_330,plain,
    ( ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_11])).

cnf(c_331,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_1786,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X0_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK2)
    | u1_struct_0(X2_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_331])).

cnf(c_2727,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(sK0(X1_54,X0_54,sK3,X0_52,sK6),u1_struct_0(X0_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(sK3,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,sK3)
    | u1_struct_0(X1_54) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1786])).

cnf(c_2839,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | m1_subset_1(sK0(X0_54,sK4,sK3,X0_52,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK4)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,X0_54,X0_52,sK3)
    | u1_struct_0(X0_54) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2727])).

cnf(c_2840,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,X0_54,X0_52,sK3)
    | u1_struct_0(X0_54) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(sK0(X0_54,sK4,sK3,X0_52,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2839])).

cnf(c_2842,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,sK5,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2840])).

cnf(c_4,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X4,X2,X3,X1)
    | k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X3,sK0(X2,X4,X1,X3,X0)) != k1_funct_1(X0,sK0(X2,X4,X1,X3,X0))
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK6)) != k1_funct_1(sK6,sK0(X2,X1,X3,X0,sK6))
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_456,plain,
    ( ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK6)) != k1_funct_1(sK6,sK0(X2,X1,X3,X0,sK6))
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_11])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK6)) != k1_funct_1(sK6,sK0(X2,X1,X3,X0,sK6))
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_1784,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | k3_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,sK0(X1_54,X0_54,X2_54,X0_52,sK6)) != k1_funct_1(sK6,sK0(X1_54,X0_54,X2_54,X0_52,sK6))
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK2)
    | u1_struct_0(X2_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_2528,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(X1_54),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK2))))
    | ~ m1_pre_topc(X1_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | k3_funct_2(u1_struct_0(X0_54),u1_struct_0(sK2),X0_52,sK0(sK2,X0_54,X1_54,X0_52,sK6)) != k1_funct_1(sK6,sK0(sK2,X0_54,X1_54,X0_52,sK6))
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,X1_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_2689,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | k3_funct_2(u1_struct_0(X0_54),u1_struct_0(sK2),X0_52,sK0(sK2,X0_54,sK3,X0_52,sK6)) != k1_funct_1(sK6,sK0(sK2,X0_54,sK3,X0_52,sK6))
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_2715,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),X0_52,sK0(sK2,sK4,sK3,X0_52,sK6)) != k1_funct_1(sK6,sK0(sK2,sK4,sK3,X0_52,sK6))
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,X0_52,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2689])).

cnf(c_2717,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(sK2,sK4,sK3,sK5,sK6)) != k1_funct_1(sK6,sK0(sK2,sK4,sK3,sK5,sK6))
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,sK5,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2715])).

cnf(c_2656,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2642])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4027,c_3612,c_2842,c_2771,c_2770,c_2717,c_2665,c_2656,c_2642,c_2527,c_42,c_9,c_41,c_10,c_39,c_12,c_38,c_13,c_37,c_14,c_36,c_15,c_35,c_16,c_34,c_17,c_32,c_19,c_31,c_20,c_30,c_21,c_29,c_22,c_28,c_23,c_27,c_24,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:18:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 1.81/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/0.98  
% 1.81/0.98  ------  iProver source info
% 1.81/0.98  
% 1.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/0.98  git: non_committed_changes: false
% 1.81/0.98  git: last_make_outside_of_git: false
% 1.81/0.98  
% 1.81/0.98  ------ 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options
% 1.81/0.98  
% 1.81/0.98  --out_options                           all
% 1.81/0.98  --tptp_safe_out                         true
% 1.81/0.98  --problem_path                          ""
% 1.81/0.98  --include_path                          ""
% 1.81/0.98  --clausifier                            res/vclausify_rel
% 1.81/0.98  --clausifier_options                    --mode clausify
% 1.81/0.98  --stdin                                 false
% 1.81/0.98  --stats_out                             all
% 1.81/0.98  
% 1.81/0.98  ------ General Options
% 1.81/0.98  
% 1.81/0.98  --fof                                   false
% 1.81/0.98  --time_out_real                         305.
% 1.81/0.98  --time_out_virtual                      -1.
% 1.81/0.98  --symbol_type_check                     false
% 1.81/0.98  --clausify_out                          false
% 1.81/0.98  --sig_cnt_out                           false
% 1.81/0.98  --trig_cnt_out                          false
% 1.81/0.98  --trig_cnt_out_tolerance                1.
% 1.81/0.98  --trig_cnt_out_sk_spl                   false
% 1.81/0.98  --abstr_cl_out                          false
% 1.81/0.98  
% 1.81/0.98  ------ Global Options
% 1.81/0.98  
% 1.81/0.98  --schedule                              default
% 1.81/0.98  --add_important_lit                     false
% 1.81/0.98  --prop_solver_per_cl                    1000
% 1.81/0.98  --min_unsat_core                        false
% 1.81/0.98  --soft_assumptions                      false
% 1.81/0.98  --soft_lemma_size                       3
% 1.81/0.98  --prop_impl_unit_size                   0
% 1.81/0.98  --prop_impl_unit                        []
% 1.81/0.98  --share_sel_clauses                     true
% 1.81/0.98  --reset_solvers                         false
% 1.81/0.98  --bc_imp_inh                            [conj_cone]
% 1.81/0.98  --conj_cone_tolerance                   3.
% 1.81/0.98  --extra_neg_conj                        none
% 1.81/0.98  --large_theory_mode                     true
% 1.81/0.98  --prolific_symb_bound                   200
% 1.81/0.98  --lt_threshold                          2000
% 1.81/0.98  --clause_weak_htbl                      true
% 1.81/0.98  --gc_record_bc_elim                     false
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing Options
% 1.81/0.98  
% 1.81/0.98  --preprocessing_flag                    true
% 1.81/0.98  --time_out_prep_mult                    0.1
% 1.81/0.98  --splitting_mode                        input
% 1.81/0.98  --splitting_grd                         true
% 1.81/0.98  --splitting_cvd                         false
% 1.81/0.98  --splitting_cvd_svl                     false
% 1.81/0.98  --splitting_nvd                         32
% 1.81/0.98  --sub_typing                            true
% 1.81/0.98  --prep_gs_sim                           true
% 1.81/0.98  --prep_unflatten                        true
% 1.81/0.98  --prep_res_sim                          true
% 1.81/0.98  --prep_upred                            true
% 1.81/0.98  --prep_sem_filter                       exhaustive
% 1.81/0.98  --prep_sem_filter_out                   false
% 1.81/0.98  --pred_elim                             true
% 1.81/0.98  --res_sim_input                         true
% 1.81/0.98  --eq_ax_congr_red                       true
% 1.81/0.98  --pure_diseq_elim                       true
% 1.81/0.98  --brand_transform                       false
% 1.81/0.98  --non_eq_to_eq                          false
% 1.81/0.98  --prep_def_merge                        true
% 1.81/0.98  --prep_def_merge_prop_impl              false
% 1.81/0.98  --prep_def_merge_mbd                    true
% 1.81/0.98  --prep_def_merge_tr_red                 false
% 1.81/0.98  --prep_def_merge_tr_cl                  false
% 1.81/0.98  --smt_preprocessing                     true
% 1.81/0.98  --smt_ac_axioms                         fast
% 1.81/0.98  --preprocessed_out                      false
% 1.81/0.98  --preprocessed_stats                    false
% 1.81/0.98  
% 1.81/0.98  ------ Abstraction refinement Options
% 1.81/0.98  
% 1.81/0.98  --abstr_ref                             []
% 1.81/0.98  --abstr_ref_prep                        false
% 1.81/0.98  --abstr_ref_until_sat                   false
% 1.81/0.98  --abstr_ref_sig_restrict                funpre
% 1.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.98  --abstr_ref_under                       []
% 1.81/0.98  
% 1.81/0.98  ------ SAT Options
% 1.81/0.98  
% 1.81/0.98  --sat_mode                              false
% 1.81/0.98  --sat_fm_restart_options                ""
% 1.81/0.98  --sat_gr_def                            false
% 1.81/0.98  --sat_epr_types                         true
% 1.81/0.98  --sat_non_cyclic_types                  false
% 1.81/0.98  --sat_finite_models                     false
% 1.81/0.98  --sat_fm_lemmas                         false
% 1.81/0.98  --sat_fm_prep                           false
% 1.81/0.98  --sat_fm_uc_incr                        true
% 1.81/0.98  --sat_out_model                         small
% 1.81/0.98  --sat_out_clauses                       false
% 1.81/0.98  
% 1.81/0.98  ------ QBF Options
% 1.81/0.98  
% 1.81/0.98  --qbf_mode                              false
% 1.81/0.98  --qbf_elim_univ                         false
% 1.81/0.98  --qbf_dom_inst                          none
% 1.81/0.98  --qbf_dom_pre_inst                      false
% 1.81/0.98  --qbf_sk_in                             false
% 1.81/0.98  --qbf_pred_elim                         true
% 1.81/0.98  --qbf_split                             512
% 1.81/0.98  
% 1.81/0.98  ------ BMC1 Options
% 1.81/0.98  
% 1.81/0.98  --bmc1_incremental                      false
% 1.81/0.98  --bmc1_axioms                           reachable_all
% 1.81/0.98  --bmc1_min_bound                        0
% 1.81/0.98  --bmc1_max_bound                        -1
% 1.81/0.98  --bmc1_max_bound_default                -1
% 1.81/0.98  --bmc1_symbol_reachability              true
% 1.81/0.98  --bmc1_property_lemmas                  false
% 1.81/0.98  --bmc1_k_induction                      false
% 1.81/0.98  --bmc1_non_equiv_states                 false
% 1.81/0.98  --bmc1_deadlock                         false
% 1.81/0.98  --bmc1_ucm                              false
% 1.81/0.98  --bmc1_add_unsat_core                   none
% 1.81/0.98  --bmc1_unsat_core_children              false
% 1.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.98  --bmc1_out_stat                         full
% 1.81/0.98  --bmc1_ground_init                      false
% 1.81/0.98  --bmc1_pre_inst_next_state              false
% 1.81/0.98  --bmc1_pre_inst_state                   false
% 1.81/0.98  --bmc1_pre_inst_reach_state             false
% 1.81/0.98  --bmc1_out_unsat_core                   false
% 1.81/0.98  --bmc1_aig_witness_out                  false
% 1.81/0.98  --bmc1_verbose                          false
% 1.81/0.98  --bmc1_dump_clauses_tptp                false
% 1.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.98  --bmc1_dump_file                        -
% 1.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.98  --bmc1_ucm_extend_mode                  1
% 1.81/0.98  --bmc1_ucm_init_mode                    2
% 1.81/0.98  --bmc1_ucm_cone_mode                    none
% 1.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.98  --bmc1_ucm_relax_model                  4
% 1.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.98  --bmc1_ucm_layered_model                none
% 1.81/0.98  --bmc1_ucm_max_lemma_size               10
% 1.81/0.98  
% 1.81/0.98  ------ AIG Options
% 1.81/0.98  
% 1.81/0.98  --aig_mode                              false
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation Options
% 1.81/0.98  
% 1.81/0.98  --instantiation_flag                    true
% 1.81/0.98  --inst_sos_flag                         false
% 1.81/0.98  --inst_sos_phase                        true
% 1.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel_side                     num_symb
% 1.81/0.98  --inst_solver_per_active                1400
% 1.81/0.98  --inst_solver_calls_frac                1.
% 1.81/0.98  --inst_passive_queue_type               priority_queues
% 1.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.98  --inst_passive_queues_freq              [25;2]
% 1.81/0.98  --inst_dismatching                      true
% 1.81/0.98  --inst_eager_unprocessed_to_passive     true
% 1.81/0.98  --inst_prop_sim_given                   true
% 1.81/0.98  --inst_prop_sim_new                     false
% 1.81/0.98  --inst_subs_new                         false
% 1.81/0.98  --inst_eq_res_simp                      false
% 1.81/0.98  --inst_subs_given                       false
% 1.81/0.98  --inst_orphan_elimination               true
% 1.81/0.98  --inst_learning_loop_flag               true
% 1.81/0.98  --inst_learning_start                   3000
% 1.81/0.98  --inst_learning_factor                  2
% 1.81/0.98  --inst_start_prop_sim_after_learn       3
% 1.81/0.98  --inst_sel_renew                        solver
% 1.81/0.98  --inst_lit_activity_flag                true
% 1.81/0.98  --inst_restr_to_given                   false
% 1.81/0.98  --inst_activity_threshold               500
% 1.81/0.98  --inst_out_proof                        true
% 1.81/0.98  
% 1.81/0.98  ------ Resolution Options
% 1.81/0.98  
% 1.81/0.98  --resolution_flag                       true
% 1.81/0.98  --res_lit_sel                           adaptive
% 1.81/0.98  --res_lit_sel_side                      none
% 1.81/0.98  --res_ordering                          kbo
% 1.81/0.98  --res_to_prop_solver                    active
% 1.81/0.98  --res_prop_simpl_new                    false
% 1.81/0.98  --res_prop_simpl_given                  true
% 1.81/0.98  --res_passive_queue_type                priority_queues
% 1.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.98  --res_passive_queues_freq               [15;5]
% 1.81/0.98  --res_forward_subs                      full
% 1.81/0.98  --res_backward_subs                     full
% 1.81/0.98  --res_forward_subs_resolution           true
% 1.81/0.98  --res_backward_subs_resolution          true
% 1.81/0.98  --res_orphan_elimination                true
% 1.81/0.98  --res_time_limit                        2.
% 1.81/0.98  --res_out_proof                         true
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Options
% 1.81/0.98  
% 1.81/0.98  --superposition_flag                    true
% 1.81/0.98  --sup_passive_queue_type                priority_queues
% 1.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.98  --demod_completeness_check              fast
% 1.81/0.98  --demod_use_ground                      true
% 1.81/0.98  --sup_to_prop_solver                    passive
% 1.81/0.98  --sup_prop_simpl_new                    true
% 1.81/0.98  --sup_prop_simpl_given                  true
% 1.81/0.98  --sup_fun_splitting                     false
% 1.81/0.98  --sup_smt_interval                      50000
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Simplification Setup
% 1.81/0.98  
% 1.81/0.98  --sup_indices_passive                   []
% 1.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_full_bw                           [BwDemod]
% 1.81/0.98  --sup_immed_triv                        [TrivRules]
% 1.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_immed_bw_main                     []
% 1.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  
% 1.81/0.98  ------ Combination Options
% 1.81/0.98  
% 1.81/0.98  --comb_res_mult                         3
% 1.81/0.98  --comb_sup_mult                         2
% 1.81/0.98  --comb_inst_mult                        10
% 1.81/0.98  
% 1.81/0.98  ------ Debug Options
% 1.81/0.98  
% 1.81/0.98  --dbg_backtrace                         false
% 1.81/0.98  --dbg_dump_prop_clauses                 false
% 1.81/0.98  --dbg_dump_prop_clauses_file            -
% 1.81/0.98  --dbg_out_stat                          false
% 1.81/0.98  ------ Parsing...
% 1.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/0.98  ------ Proving...
% 1.81/0.98  ------ Problem Properties 
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  clauses                                 25
% 1.81/0.98  conjectures                             18
% 1.81/0.98  EPR                                     15
% 1.81/0.98  Horn                                    20
% 1.81/0.98  unary                                   17
% 1.81/0.98  binary                                  0
% 1.81/0.98  lits                                    102
% 1.81/0.98  lits eq                                 13
% 1.81/0.98  fd_pure                                 0
% 1.81/0.98  fd_pseudo                               0
% 1.81/0.98  fd_cond                                 0
% 1.81/0.98  fd_pseudo_cond                          0
% 1.81/0.98  AC symbols                              0
% 1.81/0.98  
% 1.81/0.98  ------ Schedule dynamic 5 is on 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  ------ 
% 1.81/0.98  Current options:
% 1.81/0.98  ------ 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options
% 1.81/0.98  
% 1.81/0.98  --out_options                           all
% 1.81/0.98  --tptp_safe_out                         true
% 1.81/0.98  --problem_path                          ""
% 1.81/0.98  --include_path                          ""
% 1.81/0.98  --clausifier                            res/vclausify_rel
% 1.81/0.98  --clausifier_options                    --mode clausify
% 1.81/0.98  --stdin                                 false
% 1.81/0.98  --stats_out                             all
% 1.81/0.98  
% 1.81/0.98  ------ General Options
% 1.81/0.98  
% 1.81/0.98  --fof                                   false
% 1.81/0.98  --time_out_real                         305.
% 1.81/0.98  --time_out_virtual                      -1.
% 1.81/0.98  --symbol_type_check                     false
% 1.81/0.98  --clausify_out                          false
% 1.81/0.98  --sig_cnt_out                           false
% 1.81/0.98  --trig_cnt_out                          false
% 1.81/0.98  --trig_cnt_out_tolerance                1.
% 1.81/0.98  --trig_cnt_out_sk_spl                   false
% 1.81/0.98  --abstr_cl_out                          false
% 1.81/0.98  
% 1.81/0.98  ------ Global Options
% 1.81/0.98  
% 1.81/0.98  --schedule                              default
% 1.81/0.98  --add_important_lit                     false
% 1.81/0.98  --prop_solver_per_cl                    1000
% 1.81/0.98  --min_unsat_core                        false
% 1.81/0.98  --soft_assumptions                      false
% 1.81/0.98  --soft_lemma_size                       3
% 1.81/0.98  --prop_impl_unit_size                   0
% 1.81/0.98  --prop_impl_unit                        []
% 1.81/0.98  --share_sel_clauses                     true
% 1.81/0.98  --reset_solvers                         false
% 1.81/0.98  --bc_imp_inh                            [conj_cone]
% 1.81/0.98  --conj_cone_tolerance                   3.
% 1.81/0.98  --extra_neg_conj                        none
% 1.81/0.98  --large_theory_mode                     true
% 1.81/0.98  --prolific_symb_bound                   200
% 1.81/0.98  --lt_threshold                          2000
% 1.81/0.98  --clause_weak_htbl                      true
% 1.81/0.98  --gc_record_bc_elim                     false
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing Options
% 1.81/0.98  
% 1.81/0.98  --preprocessing_flag                    true
% 1.81/0.98  --time_out_prep_mult                    0.1
% 1.81/0.98  --splitting_mode                        input
% 1.81/0.98  --splitting_grd                         true
% 1.81/0.98  --splitting_cvd                         false
% 1.81/0.98  --splitting_cvd_svl                     false
% 1.81/0.98  --splitting_nvd                         32
% 1.81/0.98  --sub_typing                            true
% 1.81/0.98  --prep_gs_sim                           true
% 1.81/0.98  --prep_unflatten                        true
% 1.81/0.98  --prep_res_sim                          true
% 1.81/0.98  --prep_upred                            true
% 1.81/0.98  --prep_sem_filter                       exhaustive
% 1.81/0.98  --prep_sem_filter_out                   false
% 1.81/0.98  --pred_elim                             true
% 1.81/0.98  --res_sim_input                         true
% 1.81/0.98  --eq_ax_congr_red                       true
% 1.81/0.98  --pure_diseq_elim                       true
% 1.81/0.98  --brand_transform                       false
% 1.81/0.98  --non_eq_to_eq                          false
% 1.81/0.98  --prep_def_merge                        true
% 1.81/0.98  --prep_def_merge_prop_impl              false
% 1.81/0.98  --prep_def_merge_mbd                    true
% 1.81/0.98  --prep_def_merge_tr_red                 false
% 1.81/0.98  --prep_def_merge_tr_cl                  false
% 1.81/0.98  --smt_preprocessing                     true
% 1.81/0.98  --smt_ac_axioms                         fast
% 1.81/0.98  --preprocessed_out                      false
% 1.81/0.98  --preprocessed_stats                    false
% 1.81/0.98  
% 1.81/0.98  ------ Abstraction refinement Options
% 1.81/0.98  
% 1.81/0.98  --abstr_ref                             []
% 1.81/0.98  --abstr_ref_prep                        false
% 1.81/0.98  --abstr_ref_until_sat                   false
% 1.81/0.98  --abstr_ref_sig_restrict                funpre
% 1.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.98  --abstr_ref_under                       []
% 1.81/0.98  
% 1.81/0.98  ------ SAT Options
% 1.81/0.98  
% 1.81/0.98  --sat_mode                              false
% 1.81/0.98  --sat_fm_restart_options                ""
% 1.81/0.98  --sat_gr_def                            false
% 1.81/0.98  --sat_epr_types                         true
% 1.81/0.98  --sat_non_cyclic_types                  false
% 1.81/0.98  --sat_finite_models                     false
% 1.81/0.98  --sat_fm_lemmas                         false
% 1.81/0.98  --sat_fm_prep                           false
% 1.81/0.98  --sat_fm_uc_incr                        true
% 1.81/0.98  --sat_out_model                         small
% 1.81/0.98  --sat_out_clauses                       false
% 1.81/0.98  
% 1.81/0.98  ------ QBF Options
% 1.81/0.98  
% 1.81/0.98  --qbf_mode                              false
% 1.81/0.98  --qbf_elim_univ                         false
% 1.81/0.98  --qbf_dom_inst                          none
% 1.81/0.98  --qbf_dom_pre_inst                      false
% 1.81/0.98  --qbf_sk_in                             false
% 1.81/0.98  --qbf_pred_elim                         true
% 1.81/0.98  --qbf_split                             512
% 1.81/0.98  
% 1.81/0.98  ------ BMC1 Options
% 1.81/0.98  
% 1.81/0.98  --bmc1_incremental                      false
% 1.81/0.98  --bmc1_axioms                           reachable_all
% 1.81/0.98  --bmc1_min_bound                        0
% 1.81/0.98  --bmc1_max_bound                        -1
% 1.81/0.98  --bmc1_max_bound_default                -1
% 1.81/0.98  --bmc1_symbol_reachability              true
% 1.81/0.98  --bmc1_property_lemmas                  false
% 1.81/0.98  --bmc1_k_induction                      false
% 1.81/0.98  --bmc1_non_equiv_states                 false
% 1.81/0.98  --bmc1_deadlock                         false
% 1.81/0.98  --bmc1_ucm                              false
% 1.81/0.98  --bmc1_add_unsat_core                   none
% 1.81/0.98  --bmc1_unsat_core_children              false
% 1.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.98  --bmc1_out_stat                         full
% 1.81/0.98  --bmc1_ground_init                      false
% 1.81/0.98  --bmc1_pre_inst_next_state              false
% 1.81/0.98  --bmc1_pre_inst_state                   false
% 1.81/0.98  --bmc1_pre_inst_reach_state             false
% 1.81/0.98  --bmc1_out_unsat_core                   false
% 1.81/0.98  --bmc1_aig_witness_out                  false
% 1.81/0.98  --bmc1_verbose                          false
% 1.81/0.98  --bmc1_dump_clauses_tptp                false
% 1.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.98  --bmc1_dump_file                        -
% 1.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.98  --bmc1_ucm_extend_mode                  1
% 1.81/0.98  --bmc1_ucm_init_mode                    2
% 1.81/0.98  --bmc1_ucm_cone_mode                    none
% 1.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.98  --bmc1_ucm_relax_model                  4
% 1.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.98  --bmc1_ucm_layered_model                none
% 1.81/0.98  --bmc1_ucm_max_lemma_size               10
% 1.81/0.98  
% 1.81/0.98  ------ AIG Options
% 1.81/0.98  
% 1.81/0.98  --aig_mode                              false
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation Options
% 1.81/0.98  
% 1.81/0.98  --instantiation_flag                    true
% 1.81/0.98  --inst_sos_flag                         false
% 1.81/0.98  --inst_sos_phase                        true
% 1.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel_side                     none
% 1.81/0.98  --inst_solver_per_active                1400
% 1.81/0.98  --inst_solver_calls_frac                1.
% 1.81/0.98  --inst_passive_queue_type               priority_queues
% 1.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.98  --inst_passive_queues_freq              [25;2]
% 1.81/0.98  --inst_dismatching                      true
% 1.81/0.98  --inst_eager_unprocessed_to_passive     true
% 1.81/0.98  --inst_prop_sim_given                   true
% 1.81/0.98  --inst_prop_sim_new                     false
% 1.81/0.98  --inst_subs_new                         false
% 1.81/0.98  --inst_eq_res_simp                      false
% 1.81/0.98  --inst_subs_given                       false
% 1.81/0.98  --inst_orphan_elimination               true
% 1.81/0.98  --inst_learning_loop_flag               true
% 1.81/0.98  --inst_learning_start                   3000
% 1.81/0.98  --inst_learning_factor                  2
% 1.81/0.98  --inst_start_prop_sim_after_learn       3
% 1.81/0.98  --inst_sel_renew                        solver
% 1.81/0.98  --inst_lit_activity_flag                true
% 1.81/0.98  --inst_restr_to_given                   false
% 1.81/0.98  --inst_activity_threshold               500
% 1.81/0.98  --inst_out_proof                        true
% 1.81/0.98  
% 1.81/0.98  ------ Resolution Options
% 1.81/0.98  
% 1.81/0.98  --resolution_flag                       false
% 1.81/0.98  --res_lit_sel                           adaptive
% 1.81/0.98  --res_lit_sel_side                      none
% 1.81/0.98  --res_ordering                          kbo
% 1.81/0.98  --res_to_prop_solver                    active
% 1.81/0.98  --res_prop_simpl_new                    false
% 1.81/0.98  --res_prop_simpl_given                  true
% 1.81/0.98  --res_passive_queue_type                priority_queues
% 1.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.98  --res_passive_queues_freq               [15;5]
% 1.81/0.98  --res_forward_subs                      full
% 1.81/0.98  --res_backward_subs                     full
% 1.81/0.98  --res_forward_subs_resolution           true
% 1.81/0.98  --res_backward_subs_resolution          true
% 1.81/0.98  --res_orphan_elimination                true
% 1.81/0.98  --res_time_limit                        2.
% 1.81/0.98  --res_out_proof                         true
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Options
% 1.81/0.98  
% 1.81/0.98  --superposition_flag                    true
% 1.81/0.98  --sup_passive_queue_type                priority_queues
% 1.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.98  --demod_completeness_check              fast
% 1.81/0.98  --demod_use_ground                      true
% 1.81/0.98  --sup_to_prop_solver                    passive
% 1.81/0.98  --sup_prop_simpl_new                    true
% 1.81/0.98  --sup_prop_simpl_given                  true
% 1.81/0.98  --sup_fun_splitting                     false
% 1.81/0.98  --sup_smt_interval                      50000
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Simplification Setup
% 1.81/0.98  
% 1.81/0.98  --sup_indices_passive                   []
% 1.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_full_bw                           [BwDemod]
% 1.81/0.98  --sup_immed_triv                        [TrivRules]
% 1.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_immed_bw_main                     []
% 1.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  
% 1.81/0.98  ------ Combination Options
% 1.81/0.98  
% 1.81/0.98  --comb_res_mult                         3
% 1.81/0.98  --comb_sup_mult                         2
% 1.81/0.98  --comb_inst_mult                        10
% 1.81/0.98  
% 1.81/0.98  ------ Debug Options
% 1.81/0.98  
% 1.81/0.98  --dbg_backtrace                         false
% 1.81/0.98  --dbg_dump_prop_clauses                 false
% 1.81/0.98  --dbg_dump_prop_clauses_file            -
% 1.81/0.98  --dbg_out_stat                          false
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  ------ Proving...
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  % SZS status Theorem for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  fof(f5,axiom,(
% 1.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f15,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f5])).
% 1.81/0.98  
% 1.81/0.98  fof(f16,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.98    inference(flattening,[],[f15])).
% 1.81/0.98  
% 1.81/0.98  fof(f19,plain,(
% 1.81/0.98    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f20,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f33,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f20])).
% 1.81/0.98  
% 1.81/0.98  fof(f6,conjecture,(
% 1.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f7,negated_conjecture,(
% 1.81/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 1.81/0.98    inference(negated_conjecture,[],[f6])).
% 1.81/0.98  
% 1.81/0.98  fof(f17,plain,(
% 1.81/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f7])).
% 1.81/0.98  
% 1.81/0.98  fof(f18,plain,(
% 1.81/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.81/0.98    inference(flattening,[],[f17])).
% 1.81/0.98  
% 1.81/0.98  fof(f26,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK6) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(sK6,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f25,plain,(
% 1.81/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK5),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f24,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f23,plain,(
% 1.81/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f22,plain,(
% 1.81/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f21,plain,(
% 1.81/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f27,plain,(
% 1.81/0.98    (((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) & ! [X6] : (k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) = k1_funct_1(sK6,X6) | ~r2_hidden(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f18,f26,f25,f24,f23,f22,f21])).
% 1.81/0.98  
% 1.81/0.98  fof(f53,plain,(
% 1.81/0.98    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f49,plain,(
% 1.81/0.98    v1_funct_1(sK6)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f42,plain,(
% 1.81/0.98    m1_pre_topc(sK3,sK1)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f47,plain,(
% 1.81/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f4,axiom,(
% 1.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f13,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f4])).
% 1.81/0.98  
% 1.81/0.98  fof(f14,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.98    inference(flattening,[],[f13])).
% 1.81/0.98  
% 1.81/0.98  fof(f31,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f14])).
% 1.81/0.98  
% 1.81/0.98  fof(f38,plain,(
% 1.81/0.98    ~v2_struct_0(sK2)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f39,plain,(
% 1.81/0.98    v2_pre_topc(sK2)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f40,plain,(
% 1.81/0.98    l1_pre_topc(sK2)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f45,plain,(
% 1.81/0.98    v1_funct_1(sK5)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f46,plain,(
% 1.81/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f48,plain,(
% 1.81/0.98    m1_pre_topc(sK3,sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f3,axiom,(
% 1.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f11,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f3])).
% 1.81/0.98  
% 1.81/0.98  fof(f12,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.98    inference(flattening,[],[f11])).
% 1.81/0.98  
% 1.81/0.98  fof(f30,plain,(
% 1.81/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f12])).
% 1.81/0.98  
% 1.81/0.98  fof(f36,plain,(
% 1.81/0.98    v2_pre_topc(sK1)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f37,plain,(
% 1.81/0.98    l1_pre_topc(sK1)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f43,plain,(
% 1.81/0.98    ~v2_struct_0(sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f44,plain,(
% 1.81/0.98    m1_pre_topc(sK4,sK1)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f1,axiom,(
% 1.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f8,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f1])).
% 1.81/0.98  
% 1.81/0.98  fof(f9,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.81/0.98    inference(flattening,[],[f8])).
% 1.81/0.98  
% 1.81/0.98  fof(f28,plain,(
% 1.81/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f9])).
% 1.81/0.98  
% 1.81/0.98  fof(f2,axiom,(
% 1.81/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f10,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.81/0.98    inference(ennf_transformation,[],[f2])).
% 1.81/0.98  
% 1.81/0.98  fof(f29,plain,(
% 1.81/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f10])).
% 1.81/0.98  
% 1.81/0.98  fof(f35,plain,(
% 1.81/0.98    ~v2_struct_0(sK1)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f41,plain,(
% 1.81/0.98    ~v2_struct_0(sK3)),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f50,plain,(
% 1.81/0.98    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f51,plain,(
% 1.81/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f52,plain,(
% 1.81/0.98    ( ! [X6] : (k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) = k1_funct_1(sK6,X6) | ~r2_hidden(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK4))) )),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f32,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f20])).
% 1.81/0.98  
% 1.81/0.98  fof(f34,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f20])).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5,plain,
% 1.81/0.98      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 1.81/0.98      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 1.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 1.81/0.98      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 1.81/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.81/0.98      | ~ m1_pre_topc(X0,X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X0)
% 1.81/0.98      | ~ v1_funct_1(X4)
% 1.81/0.98      | ~ v1_funct_1(X3)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_7,negated_conjecture,
% 1.81/0.98      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
% 1.81/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_388,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 1.81/0.98      | r2_hidden(sK0(X2,X4,X1,X3,X0),u1_struct_0(X1))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X1,X4)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X4)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ v1_funct_1(X3)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X4)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X4)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X4,X2,X3,X1)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.81/0.98      | sK6 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_389,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | r2_hidden(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X3))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ v1_funct_1(sK6)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_388]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_11,negated_conjecture,
% 1.81/0.98      ( v1_funct_1(sK6) ),
% 1.81/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_393,plain,
% 1.81/0.98      ( ~ v1_funct_1(X0)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | r2_hidden(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X3))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_389,c_11]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_394,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | r2_hidden(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X3))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_393]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1785,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 1.81/0.98      | r2_hidden(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X2_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X2_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X2_54) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_394]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2260,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X2_54) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X2_54)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 1.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 1.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X0_54) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_18,negated_conjecture,
% 1.81/0.98      ( m1_pre_topc(sK3,sK1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1794,negated_conjecture,
% 1.81/0.98      ( m1_pre_topc(sK3,sK1) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2251,plain,
% 1.81/0.98      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_13,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 1.81/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1799,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2246,plain,
% 1.81/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X4)
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | ~ m1_pre_topc(X1,X4)
% 1.81/0.98      | v2_struct_0(X4)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ l1_pre_topc(X4)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X4)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1805,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 1.81/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 1.81/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X3_54)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X3_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X3_54)
% 1.81/0.98      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2240,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
% 1.81/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 1.81/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 1.81/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | v2_struct_0(X3_54) = iProver_top
% 1.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(X3_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X3_54) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3067,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK2,sK4,X0_54,sK5)
% 1.81/0.98      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 1.81/0.98      | m1_pre_topc(X0_54,sK4) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK4,X1_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v1_funct_1(sK5) != iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2246,c_2240]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_22,negated_conjecture,
% 1.81/0.98      ( ~ v2_struct_0(sK2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_29,plain,
% 1.81/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_21,negated_conjecture,
% 1.81/0.98      ( v2_pre_topc(sK2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_30,plain,
% 1.81/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_20,negated_conjecture,
% 1.81/0.98      ( l1_pre_topc(sK2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_31,plain,
% 1.81/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_15,negated_conjecture,
% 1.81/0.98      ( v1_funct_1(sK5) ),
% 1.81/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_36,plain,
% 1.81/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_14,negated_conjecture,
% 1.81/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_37,plain,
% 1.81/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3590,plain,
% 1.81/0.98      ( v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK2,sK4,X0_54,sK5)
% 1.81/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 1.81/0.98      | m1_pre_topc(X0_54,sK4) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK4,X1_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3067,c_29,c_30,c_31,c_36,c_37]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3591,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK2,sK4,X0_54,sK5)
% 1.81/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 1.81/0.98      | m1_pre_topc(X0_54,sK4) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK4,X1_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_3590]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3605,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK1,sK2,sK4,sK3,sK5)
% 1.81/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK1) = iProver_top
% 1.81/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2251,c_3591]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_12,negated_conjecture,
% 1.81/0.98      ( m1_pre_topc(sK3,sK4) ),
% 1.81/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1800,negated_conjecture,
% 1.81/0.98      ( m1_pre_topc(sK3,sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2245,plain,
% 1.81/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 1.81/0.98      inference(cnf_transformation,[],[f30]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1806,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2239,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 1.81/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 1.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X0_54) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1806]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3005,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK2,sK5,X0_54)
% 1.81/0.98      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_pre_topc(X0_54,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v1_funct_1(sK5) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2246,c_2239]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_24,negated_conjecture,
% 1.81/0.98      ( v2_pre_topc(sK1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_27,plain,
% 1.81/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_23,negated_conjecture,
% 1.81/0.98      ( l1_pre_topc(sK1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_28,plain,
% 1.81/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_17,negated_conjecture,
% 1.81/0.98      ( ~ v2_struct_0(sK4) ),
% 1.81/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_34,plain,
% 1.81/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_16,negated_conjecture,
% 1.81/0.98      ( m1_pre_topc(sK4,sK1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_35,plain,
% 1.81/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1796,negated_conjecture,
% 1.81/0.98      ( m1_pre_topc(sK4,sK1) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2249,plain,
% 1.81/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1796]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_0,plain,
% 1.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | v2_pre_topc(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f28]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1808,plain,
% 1.81/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | v2_pre_topc(X0_54) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2237,plain,
% 1.81/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X0_54) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1808]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2642,plain,
% 1.81/0.98      ( l1_pre_topc(sK1) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) = iProver_top
% 1.81/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2249,c_2237]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1,plain,
% 1.81/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1807,plain,
% 1.81/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | l1_pre_topc(X0_54) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2621,plain,
% 1.81/0.98      ( ~ m1_pre_topc(sK4,X0_54)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | l1_pre_topc(sK4) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1807]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2770,plain,
% 1.81/0.98      ( ~ m1_pre_topc(sK4,sK1) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK1) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2621]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2771,plain,
% 1.81/0.98      ( m1_pre_topc(sK4,sK1) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) = iProver_top
% 1.81/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3223,plain,
% 1.81/0.98      ( m1_pre_topc(X0_54,sK4) != iProver_top
% 1.81/0.98      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK2,sK5,X0_54) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3005,c_27,c_28,c_29,c_30,c_31,c_34,c_35,c_36,c_37,
% 1.81/0.98                 c_2642,c_2771]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3224,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK2,sK5,X0_54)
% 1.81/0.98      | m1_pre_topc(X0_54,sK4) != iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_3223]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3231,plain,
% 1.81/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2245,c_3224]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3612,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
% 1.81/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK1) = iProver_top
% 1.81/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_3605,c_3231]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_25,negated_conjecture,
% 1.81/0.98      ( ~ v2_struct_0(sK1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_26,plain,
% 1.81/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_39,plain,
% 1.81/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3722,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3612,c_26,c_27,c_28,c_35,c_39]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3730,plain,
% 1.81/0.98      ( k2_tmap_1(X0_54,X1_54,X0_52,X2_54) != k2_tmap_1(sK4,sK2,sK5,sK3)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X2_54) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X2_54)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 1.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 1.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 1.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 1.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 1.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(X0_54) != iProver_top ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2260,c_3722]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3751,plain,
% 1.81/0.98      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v2_struct_0(sK3) = iProver_top
% 1.81/0.98      | v1_funct_1(sK5) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(equality_resolution,[status(thm)],[c_3730]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4020,plain,
% 1.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v2_struct_0(sK3) = iProver_top
% 1.81/0.98      | v1_funct_1(sK5) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(equality_resolution_simp,[status(thm)],[c_3751]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_19,negated_conjecture,
% 1.81/0.98      ( ~ v2_struct_0(sK3) ),
% 1.81/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_32,plain,
% 1.81/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_38,plain,
% 1.81/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_10,negated_conjecture,
% 1.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_41,plain,
% 1.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_9,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 1.81/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_42,plain,
% 1.81/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1810,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2527,plain,
% 1.81/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1810]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2665,plain,
% 1.81/0.98      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1810]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2530,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X1_54),u1_struct_0(sK2))
% 1.81/0.98      | r2_hidden(sK0(sK2,X0_54,X1_54,X0_52,sK6),u1_struct_0(X1_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(X1_54,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,X1_54)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1785]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2686,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 1.81/0.98      | r2_hidden(sK0(sK2,X0_54,sK3,X0_52,sK6),u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,X0_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2530]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2741,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 1.81/0.98      | r2_hidden(sK0(sK2,sK4,sK3,X0_52,sK6),u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,sK4)
% 1.81/0.98      | v2_struct_0(sK4)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(sK4)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(sK4)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2686]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2742,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,sK4,sK3,X0_52,sK6),u1_struct_0(sK3)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v2_struct_0(sK3) = iProver_top
% 1.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2741]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2744,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,sK5,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v2_struct_0(sK3) = iProver_top
% 1.81/0.98      | v1_funct_1(sK5) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2742]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4022,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK3)) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_4020,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_34,c_35,
% 1.81/0.98                 c_36,c_37,c_38,c_39,c_41,c_42,c_2527,c_2642,c_2665,
% 1.81/0.98                 c_2744,c_2771,c_3612]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_8,negated_conjecture,
% 1.81/0.98      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.81/0.98      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK6,X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1804,negated_conjecture,
% 1.81/0.98      ( ~ r2_hidden(X0_52,u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.81/0.98      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_52) = k1_funct_1(sK6,X0_52) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2241,plain,
% 1.81/0.98      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_52) = k1_funct_1(sK6,X0_52)
% 1.81/0.98      | r2_hidden(X0_52,u1_struct_0(sK3)) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4027,plain,
% 1.81/0.98      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(sK2,sK4,sK3,sK5,sK6)) = k1_funct_1(sK6,sK0(sK2,sK4,sK3,sK5,sK6))
% 1.81/0.98      | m1_subset_1(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_4022,c_2241]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_6,plain,
% 1.81/0.98      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 1.81/0.98      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 1.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 1.81/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.81/0.98      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_pre_topc(X0,X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X0)
% 1.81/0.98      | ~ v1_funct_1(X4)
% 1.81/0.98      | ~ v1_funct_1(X3)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_325,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 1.81/0.98      | m1_subset_1(sK0(X2,X4,X1,X3,X0),u1_struct_0(X4))
% 1.81/0.98      | ~ m1_pre_topc(X1,X4)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X4)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ v1_funct_1(X3)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X4)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X4)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X4,X2,X3,X1)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.81/0.98      | sK6 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_326,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | m1_subset_1(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X1))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ v1_funct_1(sK6)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_325]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_330,plain,
% 1.81/0.98      ( ~ v1_funct_1(X0)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | m1_subset_1(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X1))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_326,c_11]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_331,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | m1_subset_1(sK0(X2,X1,X3,X0,sK6),u1_struct_0(X1))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_330]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1786,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 1.81/0.98      | m1_subset_1(sK0(X1_54,X0_54,X2_54,X0_52,sK6),u1_struct_0(X0_54))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X2_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X2_54) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_331]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2727,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X1_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 1.81/0.98      | m1_subset_1(sK0(X1_54,X0_54,sK3,X0_52,sK6),u1_struct_0(X0_54))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1786]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2839,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(X0_54))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 1.81/0.98      | m1_subset_1(sK0(X0_54,sK4,sK3,X0_52,sK6),u1_struct_0(sK4))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,sK4)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | v2_struct_0(sK4)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ l1_pre_topc(sK4)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(sK4)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,X0_54,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(X0_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2727]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2840,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,X0_54,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(X0_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK0(X0_54,sK4,sK3,X0_52,sK6),u1_struct_0(sK4)) = iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK3) = iProver_top
% 1.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 1.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2839]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2842,plain,
% 1.81/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,sK5,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(sK0(sK2,sK4,sK3,sK5,sK6),u1_struct_0(sK4)) = iProver_top
% 1.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.81/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.81/0.98      | v2_struct_0(sK4) = iProver_top
% 1.81/0.98      | v2_struct_0(sK2) = iProver_top
% 1.81/0.98      | v2_struct_0(sK3) = iProver_top
% 1.81/0.98      | v1_funct_1(sK5) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK4) != iProver_top
% 1.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK4) != iProver_top
% 1.81/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2840]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4,plain,
% 1.81/0.98      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 1.81/0.98      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 1.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 1.81/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.81/0.98      | ~ m1_pre_topc(X0,X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X0)
% 1.81/0.98      | ~ v1_funct_1(X4)
% 1.81/0.98      | ~ v1_funct_1(X3)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_451,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X1,X4)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X4)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ v1_funct_1(X3)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X4)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X4)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X4,X2,X3,X1)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X3,sK0(X2,X4,X1,X3,X0)) != k1_funct_1(X0,sK0(X2,X4,X1,X3,X0))
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.81/0.98      | sK6 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_452,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ v1_funct_1(sK6)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK6)) != k1_funct_1(sK6,sK0(X2,X1,X3,X0,sK6))
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_451]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_456,plain,
% 1.81/0.98      ( ~ v1_funct_1(X0)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK6)) != k1_funct_1(sK6,sK0(X2,X1,X3,X0,sK6))
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_452,c_11]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_457,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X2))
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.81/0.98      | ~ m1_pre_topc(X3,X1)
% 1.81/0.98      | v2_struct_0(X1)
% 1.81/0.98      | v2_struct_0(X2)
% 1.81/0.98      | v2_struct_0(X3)
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | ~ l1_pre_topc(X1)
% 1.81/0.98      | ~ l1_pre_topc(X2)
% 1.81/0.98      | ~ v2_pre_topc(X1)
% 1.81/0.98      | ~ v2_pre_topc(X2)
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X1,X2,X0,X3)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK6)) != k1_funct_1(sK6,sK0(X2,X1,X3,X0,sK6))
% 1.81/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_456]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1784,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 1.81/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X2_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X1_54)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(X1_54)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,sK0(X1_54,X0_54,X2_54,X0_52,sK6)) != k1_funct_1(sK6,sK0(X1_54,X0_54,X2_54,X0_52,sK6))
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(X2_54) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_457]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2528,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(X1_54),u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(X1_54,X0_54)
% 1.81/0.98      | v2_struct_0(X1_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X0_54),u1_struct_0(sK2),X0_52,sK0(sK2,X0_54,X1_54,X0_52,sK6)) != k1_funct_1(sK6,sK0(sK2,X0_54,X1_54,X0_52,sK6))
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,X1_54)
% 1.81/0.98      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1784]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2689,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,X0_54)
% 1.81/0.98      | v2_struct_0(X0_54)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(X0_54)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(X0_54)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_funct_2(u1_struct_0(X0_54),u1_struct_0(sK2),X0_52,sK0(sK2,X0_54,sK3,X0_52,sK6)) != k1_funct_1(sK6,sK0(sK2,X0_54,sK3,X0_52,sK6))
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(X0_54,sK2,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2528]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2715,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(sK4),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,sK4)
% 1.81/0.98      | v2_struct_0(sK4)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(X0_52)
% 1.81/0.98      | ~ l1_pre_topc(sK4)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(sK4)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),X0_52,sK0(sK2,sK4,sK3,X0_52,sK6)) != k1_funct_1(sK6,sK0(sK2,sK4,sK3,X0_52,sK6))
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,X0_52,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2689]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2717,plain,
% 1.81/0.98      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 1.81/0.98      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 1.81/0.98      | ~ m1_pre_topc(sK3,sK4)
% 1.81/0.98      | v2_struct_0(sK4)
% 1.81/0.98      | v2_struct_0(sK2)
% 1.81/0.98      | v2_struct_0(sK3)
% 1.81/0.98      | ~ v1_funct_1(sK5)
% 1.81/0.98      | ~ l1_pre_topc(sK4)
% 1.81/0.98      | ~ l1_pre_topc(sK2)
% 1.81/0.98      | ~ v2_pre_topc(sK4)
% 1.81/0.98      | ~ v2_pre_topc(sK2)
% 1.81/0.98      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(sK2,sK4,sK3,sK5,sK6)) != k1_funct_1(sK6,sK0(sK2,sK4,sK3,sK5,sK6))
% 1.81/0.98      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k2_tmap_1(sK4,sK2,sK5,sK3)
% 1.81/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.81/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2715]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2656,plain,
% 1.81/0.98      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK4) | ~ v2_pre_topc(sK1) ),
% 1.81/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2642]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(contradiction,plain,
% 1.81/0.98      ( $false ),
% 1.81/0.98      inference(minisat,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_4027,c_3612,c_2842,c_2771,c_2770,c_2717,c_2665,c_2656,
% 1.81/0.98                 c_2642,c_2527,c_42,c_9,c_41,c_10,c_39,c_12,c_38,c_13,
% 1.81/0.98                 c_37,c_14,c_36,c_15,c_35,c_16,c_34,c_17,c_32,c_19,c_31,
% 1.81/0.98                 c_20,c_30,c_21,c_29,c_22,c_28,c_23,c_27,c_24,c_26]) ).
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/0.99  
% 1.81/0.99  ------                               Statistics
% 1.81/0.99  
% 1.81/0.99  ------ General
% 1.81/0.99  
% 1.81/0.99  abstr_ref_over_cycles:                  0
% 1.81/0.99  abstr_ref_under_cycles:                 0
% 1.81/0.99  gc_basic_clause_elim:                   0
% 1.81/0.99  forced_gc_time:                         0
% 1.81/0.99  parsing_time:                           0.011
% 1.81/0.99  unif_index_cands_time:                  0.
% 1.81/0.99  unif_index_add_time:                    0.
% 1.81/0.99  orderings_time:                         0.
% 1.81/0.99  out_proof_time:                         0.012
% 1.81/0.99  total_time:                             0.162
% 1.81/0.99  num_of_symbols:                         58
% 1.81/0.99  num_of_terms:                           2478
% 1.81/0.99  
% 1.81/0.99  ------ Preprocessing
% 1.81/0.99  
% 1.81/0.99  num_of_splits:                          0
% 1.81/0.99  num_of_split_atoms:                     0
% 1.81/0.99  num_of_reused_defs:                     0
% 1.81/0.99  num_eq_ax_congr_red:                    48
% 1.81/0.99  num_of_sem_filtered_clauses:            1
% 1.81/0.99  num_of_subtypes:                        6
% 1.81/0.99  monotx_restored_types:                  0
% 1.81/0.99  sat_num_of_epr_types:                   0
% 1.81/0.99  sat_num_of_non_cyclic_types:            0
% 1.81/0.99  sat_guarded_non_collapsed_types:        0
% 1.81/0.99  num_pure_diseq_elim:                    0
% 1.81/0.99  simp_replaced_by:                       0
% 1.81/0.99  res_preprocessed:                       130
% 1.81/0.99  prep_upred:                             0
% 1.81/0.99  prep_unflattend:                        26
% 1.81/0.99  smt_new_axioms:                         0
% 1.81/0.99  pred_elim_cands:                        8
% 1.81/0.99  pred_elim:                              1
% 1.81/0.99  pred_elim_cl:                           1
% 1.81/0.99  pred_elim_cycles:                       6
% 1.81/0.99  merged_defs:                            0
% 1.81/0.99  merged_defs_ncl:                        0
% 1.81/0.99  bin_hyper_res:                          0
% 1.81/0.99  prep_cycles:                            4
% 1.81/0.99  pred_elim_time:                         0.042
% 1.81/0.99  splitting_time:                         0.
% 1.81/0.99  sem_filter_time:                        0.
% 1.81/0.99  monotx_time:                            0.
% 1.81/0.99  subtype_inf_time:                       0.
% 1.81/0.99  
% 1.81/0.99  ------ Problem properties
% 1.81/0.99  
% 1.81/0.99  clauses:                                25
% 1.81/0.99  conjectures:                            18
% 1.81/0.99  epr:                                    15
% 1.81/0.99  horn:                                   20
% 1.81/0.99  ground:                                 17
% 1.81/0.99  unary:                                  17
% 1.81/0.99  binary:                                 0
% 1.81/0.99  lits:                                   102
% 1.81/0.99  lits_eq:                                13
% 1.81/0.99  fd_pure:                                0
% 1.81/0.99  fd_pseudo:                              0
% 1.81/0.99  fd_cond:                                0
% 1.81/0.99  fd_pseudo_cond:                         0
% 1.81/0.99  ac_symbols:                             0
% 1.81/0.99  
% 1.81/0.99  ------ Propositional Solver
% 1.81/0.99  
% 1.81/0.99  prop_solver_calls:                      29
% 1.81/0.99  prop_fast_solver_calls:                 1692
% 1.81/0.99  smt_solver_calls:                       0
% 1.81/0.99  smt_fast_solver_calls:                  0
% 1.81/0.99  prop_num_of_clauses:                    637
% 1.81/0.99  prop_preprocess_simplified:             3393
% 1.81/0.99  prop_fo_subsumed:                       76
% 1.81/0.99  prop_solver_time:                       0.
% 1.81/0.99  smt_solver_time:                        0.
% 1.81/0.99  smt_fast_solver_time:                   0.
% 1.81/0.99  prop_fast_solver_time:                  0.
% 1.81/0.99  prop_unsat_core_time:                   0.
% 1.81/0.99  
% 1.81/0.99  ------ QBF
% 1.81/0.99  
% 1.81/0.99  qbf_q_res:                              0
% 1.81/0.99  qbf_num_tautologies:                    0
% 1.81/0.99  qbf_prep_cycles:                        0
% 1.81/0.99  
% 1.81/0.99  ------ BMC1
% 1.81/0.99  
% 1.81/0.99  bmc1_current_bound:                     -1
% 1.81/0.99  bmc1_last_solved_bound:                 -1
% 1.81/0.99  bmc1_unsat_core_size:                   -1
% 1.81/0.99  bmc1_unsat_core_parents_size:           -1
% 1.81/0.99  bmc1_merge_next_fun:                    0
% 1.81/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.81/0.99  
% 1.81/0.99  ------ Instantiation
% 1.81/0.99  
% 1.81/0.99  inst_num_of_clauses:                    220
% 1.81/0.99  inst_num_in_passive:                    25
% 1.81/0.99  inst_num_in_active:                     195
% 1.81/0.99  inst_num_in_unprocessed:                0
% 1.81/0.99  inst_num_of_loops:                      210
% 1.81/0.99  inst_num_of_learning_restarts:          0
% 1.81/0.99  inst_num_moves_active_passive:          8
% 1.81/0.99  inst_lit_activity:                      0
% 1.81/0.99  inst_lit_activity_moves:                0
% 1.81/0.99  inst_num_tautologies:                   0
% 1.81/0.99  inst_num_prop_implied:                  0
% 1.81/0.99  inst_num_existing_simplified:           0
% 1.81/0.99  inst_num_eq_res_simplified:             0
% 1.81/0.99  inst_num_child_elim:                    0
% 1.81/0.99  inst_num_of_dismatching_blockings:      24
% 1.81/0.99  inst_num_of_non_proper_insts:           266
% 1.81/0.99  inst_num_of_duplicates:                 0
% 1.81/0.99  inst_inst_num_from_inst_to_res:         0
% 1.81/0.99  inst_dismatching_checking_time:         0.
% 1.81/0.99  
% 1.81/0.99  ------ Resolution
% 1.81/0.99  
% 1.81/0.99  res_num_of_clauses:                     0
% 1.81/0.99  res_num_in_passive:                     0
% 1.81/0.99  res_num_in_active:                      0
% 1.81/0.99  res_num_of_loops:                       134
% 1.81/0.99  res_forward_subset_subsumed:            73
% 1.81/0.99  res_backward_subset_subsumed:           0
% 1.81/0.99  res_forward_subsumed:                   0
% 1.81/0.99  res_backward_subsumed:                  0
% 1.81/0.99  res_forward_subsumption_resolution:     0
% 1.81/0.99  res_backward_subsumption_resolution:    0
% 1.81/0.99  res_clause_to_clause_subsumption:       280
% 1.81/0.99  res_orphan_elimination:                 0
% 1.81/0.99  res_tautology_del:                      81
% 1.81/0.99  res_num_eq_res_simplified:              0
% 1.81/0.99  res_num_sel_changes:                    0
% 1.81/0.99  res_moves_from_active_to_pass:          0
% 1.81/0.99  
% 1.81/0.99  ------ Superposition
% 1.81/0.99  
% 1.81/0.99  sup_time_total:                         0.
% 1.81/0.99  sup_time_generating:                    0.
% 1.81/0.99  sup_time_sim_full:                      0.
% 1.81/0.99  sup_time_sim_immed:                     0.
% 1.81/0.99  
% 1.81/0.99  sup_num_of_clauses:                     43
% 1.81/0.99  sup_num_in_active:                      41
% 1.81/0.99  sup_num_in_passive:                     2
% 1.81/0.99  sup_num_of_loops:                       41
% 1.81/0.99  sup_fw_superposition:                   16
% 1.81/0.99  sup_bw_superposition:                   2
% 1.81/0.99  sup_immediate_simplified:               2
% 1.81/0.99  sup_given_eliminated:                   0
% 1.81/0.99  comparisons_done:                       0
% 1.81/0.99  comparisons_avoided:                    0
% 1.81/0.99  
% 1.81/0.99  ------ Simplifications
% 1.81/0.99  
% 1.81/0.99  
% 1.81/0.99  sim_fw_subset_subsumed:                 0
% 1.81/0.99  sim_bw_subset_subsumed:                 0
% 1.81/0.99  sim_fw_subsumed:                        0
% 1.81/0.99  sim_bw_subsumed:                        0
% 1.81/0.99  sim_fw_subsumption_res:                 0
% 1.81/0.99  sim_bw_subsumption_res:                 0
% 1.81/0.99  sim_tautology_del:                      0
% 1.81/0.99  sim_eq_tautology_del:                   0
% 1.81/0.99  sim_eq_res_simp:                        1
% 1.81/0.99  sim_fw_demodulated:                     0
% 1.81/0.99  sim_bw_demodulated:                     1
% 1.81/0.99  sim_light_normalised:                   4
% 1.81/0.99  sim_joinable_taut:                      0
% 1.81/0.99  sim_joinable_simp:                      0
% 1.81/0.99  sim_ac_normalised:                      0
% 1.81/0.99  sim_smt_subsumption:                    0
% 1.81/0.99  
%------------------------------------------------------------------------------
