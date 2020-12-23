%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:18 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 424 expanded)
%              Number of clauses        :   43 (  52 expanded)
%              Number of leaves         :   14 ( 205 expanded)
%              Depth                    :   12
%              Number of atoms          :  720 (7066 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( v5_pre_topc(X4,X0,X1)
                              & r1_tmap_1(X2,X0,X3,X5) )
                           => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( v5_pre_topc(X4,X0,X1)
                                & r1_tmap_1(X2,X0,X3,X5) )
                             => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
          & v5_pre_topc(X4,X0,X1)
          & r1_tmap_1(X2,X0,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),sK7)
        & v5_pre_topc(X4,X0,X1)
        & r1_tmap_1(X2,X0,X3,sK7)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
              & v5_pre_topc(X4,X0,X1)
              & r1_tmap_1(X2,X0,X3,X5)
              & m1_subset_1(X5,u1_struct_0(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,sK6),X5)
            & v5_pre_topc(sK6,X0,X1)
            & r1_tmap_1(X2,X0,X3,X5)
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                  & v5_pre_topc(X4,X0,X1)
                  & r1_tmap_1(X2,X0,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(X2)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),sK5,X4),X5)
                & v5_pre_topc(X4,X0,X1)
                & r1_tmap_1(X2,X0,sK5,X5)
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                      & v5_pre_topc(X4,X0,X1)
                      & r1_tmap_1(X2,X0,X3,X5)
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_tmap_1(sK4,X1,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                    & v5_pre_topc(X4,X0,X1)
                    & r1_tmap_1(sK4,X0,X3,X5)
                    & m1_subset_1(X5,u1_struct_0(sK4)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK3),X3,X4),X5)
                        & v5_pre_topc(X4,X0,sK3)
                        & r1_tmap_1(X2,X0,X3,X5)
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                            & v5_pre_topc(X4,X0,X1)
                            & r1_tmap_1(X2,X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,sK2,X1)
                          & r1_tmap_1(X2,sK2,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
    & v5_pre_topc(sK6,sK2,sK3)
    & r1_tmap_1(sK4,sK2,sK5,sK7)
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f32,f31,f30,f29,f28,f27])).

fof(f59,plain,(
    v5_pre_topc(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f60,plain,(
    ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,negated_conjecture,
    ( v5_pre_topc(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_339,plain,
    ( r1_tmap_1(sK2,sK3,sK6,X0)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[status(thm)],[c_6,c_9])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_343,plain,
    ( r1_tmap_1(sK2,sK3,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_26,c_25,c_24,c_23,c_22,c_21,c_14,c_13,c_12])).

cnf(c_518,plain,
    ( r1_tmap_1(sK2,sK3,sK6,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_759,plain,
    ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_541,plain,
    ( v2_struct_0(X0_50)
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v1_xboole_0(sK0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_749,plain,
    ( v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_540,plain,
    ( m1_subset_1(sK0(X0_50),k1_zfmisc_1(u1_struct_0(X0_50)))
    | v2_struct_0(X0_50)
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_743,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_xboole_0(X1_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0_51)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_742,plain,
    ( ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_542,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ m1_subset_1(X3_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | m1_subset_1(k3_funct_2(X1_51,X2_51,X0_51,X3_51),X2_51)
    | ~ v1_funct_1(X0_51)
    | v1_xboole_0(X1_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_658,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(sK4),X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_51)))
    | m1_subset_1(k3_funct_2(u1_struct_0(sK4),X1_51,X0_51,sK7),X1_51)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ v1_funct_1(X0_51)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_738,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_7,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_539,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
    | ~ r1_tmap_1(X1_50,X2_50,X2_51,k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,X1_51))
    | r1_tmap_1(X0_50,X2_50,k1_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),u1_struct_0(X1_50),u1_struct_0(X2_50),X0_51,X2_51),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X2_51,u1_struct_0(X1_50),u1_struct_0(X2_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X2_50))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,X1_51),u1_struct_0(X1_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X2_51)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_684,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_50),X1_51,sK7))
    | ~ r1_tmap_1(sK4,X0_50,X1_51,sK7)
    | r1_tmap_1(sK4,X1_50,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50),X1_51,X0_51),sK7)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X1_51,u1_struct_0(sK4),u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_50),X1_51,sK7),u1_struct_0(X0_50))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(X1_51)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_710,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_759,c_749,c_743,c_742,c_738,c_710,c_8,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.99/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/0.98  
% 0.99/0.98  ------  iProver source info
% 0.99/0.98  
% 0.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/0.98  git: non_committed_changes: false
% 0.99/0.98  git: last_make_outside_of_git: false
% 0.99/0.98  
% 0.99/0.98  ------ 
% 0.99/0.98  
% 0.99/0.98  ------ Input Options
% 0.99/0.98  
% 0.99/0.98  --out_options                           all
% 0.99/0.98  --tptp_safe_out                         true
% 0.99/0.98  --problem_path                          ""
% 0.99/0.98  --include_path                          ""
% 0.99/0.98  --clausifier                            res/vclausify_rel
% 0.99/0.98  --clausifier_options                    --mode clausify
% 0.99/0.98  --stdin                                 false
% 0.99/0.98  --stats_out                             all
% 0.99/0.98  
% 0.99/0.98  ------ General Options
% 0.99/0.98  
% 0.99/0.98  --fof                                   false
% 0.99/0.98  --time_out_real                         305.
% 0.99/0.98  --time_out_virtual                      -1.
% 0.99/0.98  --symbol_type_check                     false
% 0.99/0.98  --clausify_out                          false
% 0.99/0.98  --sig_cnt_out                           false
% 0.99/0.98  --trig_cnt_out                          false
% 0.99/0.98  --trig_cnt_out_tolerance                1.
% 0.99/0.98  --trig_cnt_out_sk_spl                   false
% 0.99/0.98  --abstr_cl_out                          false
% 0.99/0.98  
% 0.99/0.98  ------ Global Options
% 0.99/0.98  
% 0.99/0.98  --schedule                              default
% 0.99/0.98  --add_important_lit                     false
% 0.99/0.98  --prop_solver_per_cl                    1000
% 0.99/0.98  --min_unsat_core                        false
% 0.99/0.98  --soft_assumptions                      false
% 0.99/0.98  --soft_lemma_size                       3
% 0.99/0.98  --prop_impl_unit_size                   0
% 0.99/0.98  --prop_impl_unit                        []
% 0.99/0.98  --share_sel_clauses                     true
% 0.99/0.98  --reset_solvers                         false
% 0.99/0.98  --bc_imp_inh                            [conj_cone]
% 0.99/0.98  --conj_cone_tolerance                   3.
% 0.99/0.98  --extra_neg_conj                        none
% 0.99/0.98  --large_theory_mode                     true
% 0.99/0.98  --prolific_symb_bound                   200
% 0.99/0.98  --lt_threshold                          2000
% 0.99/0.98  --clause_weak_htbl                      true
% 0.99/0.98  --gc_record_bc_elim                     false
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing Options
% 0.99/0.98  
% 0.99/0.98  --preprocessing_flag                    true
% 0.99/0.98  --time_out_prep_mult                    0.1
% 0.99/0.98  --splitting_mode                        input
% 0.99/0.98  --splitting_grd                         true
% 0.99/0.98  --splitting_cvd                         false
% 0.99/0.98  --splitting_cvd_svl                     false
% 0.99/0.98  --splitting_nvd                         32
% 0.99/0.98  --sub_typing                            true
% 0.99/0.98  --prep_gs_sim                           true
% 0.99/0.98  --prep_unflatten                        true
% 0.99/0.98  --prep_res_sim                          true
% 0.99/0.98  --prep_upred                            true
% 0.99/0.98  --prep_sem_filter                       exhaustive
% 0.99/0.98  --prep_sem_filter_out                   false
% 0.99/0.98  --pred_elim                             true
% 0.99/0.98  --res_sim_input                         true
% 0.99/0.98  --eq_ax_congr_red                       true
% 0.99/0.98  --pure_diseq_elim                       true
% 0.99/0.98  --brand_transform                       false
% 0.99/0.98  --non_eq_to_eq                          false
% 0.99/0.98  --prep_def_merge                        true
% 0.99/0.98  --prep_def_merge_prop_impl              false
% 0.99/0.98  --prep_def_merge_mbd                    true
% 0.99/0.98  --prep_def_merge_tr_red                 false
% 0.99/0.98  --prep_def_merge_tr_cl                  false
% 0.99/0.98  --smt_preprocessing                     true
% 0.99/0.98  --smt_ac_axioms                         fast
% 0.99/0.98  --preprocessed_out                      false
% 0.99/0.98  --preprocessed_stats                    false
% 0.99/0.98  
% 0.99/0.98  ------ Abstraction refinement Options
% 0.99/0.98  
% 0.99/0.98  --abstr_ref                             []
% 0.99/0.98  --abstr_ref_prep                        false
% 0.99/0.98  --abstr_ref_until_sat                   false
% 0.99/0.98  --abstr_ref_sig_restrict                funpre
% 0.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/0.98  --abstr_ref_under                       []
% 0.99/0.98  
% 0.99/0.98  ------ SAT Options
% 0.99/0.98  
% 0.99/0.98  --sat_mode                              false
% 0.99/0.98  --sat_fm_restart_options                ""
% 0.99/0.98  --sat_gr_def                            false
% 0.99/0.98  --sat_epr_types                         true
% 0.99/0.98  --sat_non_cyclic_types                  false
% 0.99/0.98  --sat_finite_models                     false
% 0.99/0.98  --sat_fm_lemmas                         false
% 0.99/0.98  --sat_fm_prep                           false
% 0.99/0.98  --sat_fm_uc_incr                        true
% 0.99/0.98  --sat_out_model                         small
% 0.99/0.98  --sat_out_clauses                       false
% 0.99/0.98  
% 0.99/0.98  ------ QBF Options
% 0.99/0.98  
% 0.99/0.98  --qbf_mode                              false
% 0.99/0.98  --qbf_elim_univ                         false
% 0.99/0.98  --qbf_dom_inst                          none
% 0.99/0.98  --qbf_dom_pre_inst                      false
% 0.99/0.98  --qbf_sk_in                             false
% 0.99/0.98  --qbf_pred_elim                         true
% 0.99/0.98  --qbf_split                             512
% 0.99/0.98  
% 0.99/0.98  ------ BMC1 Options
% 0.99/0.98  
% 0.99/0.98  --bmc1_incremental                      false
% 0.99/0.98  --bmc1_axioms                           reachable_all
% 0.99/0.98  --bmc1_min_bound                        0
% 0.99/0.98  --bmc1_max_bound                        -1
% 0.99/0.98  --bmc1_max_bound_default                -1
% 0.99/0.98  --bmc1_symbol_reachability              true
% 0.99/0.98  --bmc1_property_lemmas                  false
% 0.99/0.98  --bmc1_k_induction                      false
% 0.99/0.98  --bmc1_non_equiv_states                 false
% 0.99/0.98  --bmc1_deadlock                         false
% 0.99/0.98  --bmc1_ucm                              false
% 0.99/0.98  --bmc1_add_unsat_core                   none
% 0.99/0.98  --bmc1_unsat_core_children              false
% 0.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/0.98  --bmc1_out_stat                         full
% 0.99/0.98  --bmc1_ground_init                      false
% 0.99/0.98  --bmc1_pre_inst_next_state              false
% 0.99/0.98  --bmc1_pre_inst_state                   false
% 0.99/0.98  --bmc1_pre_inst_reach_state             false
% 0.99/0.98  --bmc1_out_unsat_core                   false
% 0.99/0.98  --bmc1_aig_witness_out                  false
% 0.99/0.98  --bmc1_verbose                          false
% 0.99/0.98  --bmc1_dump_clauses_tptp                false
% 0.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.99/0.98  --bmc1_dump_file                        -
% 0.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.99/0.98  --bmc1_ucm_extend_mode                  1
% 0.99/0.98  --bmc1_ucm_init_mode                    2
% 0.99/0.98  --bmc1_ucm_cone_mode                    none
% 0.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.99/0.98  --bmc1_ucm_relax_model                  4
% 0.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/0.98  --bmc1_ucm_layered_model                none
% 0.99/0.98  --bmc1_ucm_max_lemma_size               10
% 0.99/0.98  
% 0.99/0.98  ------ AIG Options
% 0.99/0.98  
% 0.99/0.98  --aig_mode                              false
% 0.99/0.98  
% 0.99/0.98  ------ Instantiation Options
% 0.99/0.98  
% 0.99/0.98  --instantiation_flag                    true
% 0.99/0.98  --inst_sos_flag                         false
% 0.99/0.98  --inst_sos_phase                        true
% 0.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel_side                     num_symb
% 0.99/0.98  --inst_solver_per_active                1400
% 0.99/0.98  --inst_solver_calls_frac                1.
% 0.99/0.98  --inst_passive_queue_type               priority_queues
% 0.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/0.98  --inst_passive_queues_freq              [25;2]
% 0.99/0.98  --inst_dismatching                      true
% 0.99/0.98  --inst_eager_unprocessed_to_passive     true
% 0.99/0.98  --inst_prop_sim_given                   true
% 0.99/0.98  --inst_prop_sim_new                     false
% 0.99/0.98  --inst_subs_new                         false
% 0.99/0.98  --inst_eq_res_simp                      false
% 0.99/0.98  --inst_subs_given                       false
% 0.99/0.98  --inst_orphan_elimination               true
% 0.99/0.98  --inst_learning_loop_flag               true
% 0.99/0.98  --inst_learning_start                   3000
% 0.99/0.98  --inst_learning_factor                  2
% 0.99/0.98  --inst_start_prop_sim_after_learn       3
% 0.99/0.98  --inst_sel_renew                        solver
% 0.99/0.98  --inst_lit_activity_flag                true
% 0.99/0.98  --inst_restr_to_given                   false
% 0.99/0.98  --inst_activity_threshold               500
% 0.99/0.98  --inst_out_proof                        true
% 0.99/0.98  
% 0.99/0.98  ------ Resolution Options
% 0.99/0.98  
% 0.99/0.98  --resolution_flag                       true
% 0.99/0.98  --res_lit_sel                           adaptive
% 0.99/0.98  --res_lit_sel_side                      none
% 0.99/0.98  --res_ordering                          kbo
% 0.99/0.98  --res_to_prop_solver                    active
% 0.99/0.98  --res_prop_simpl_new                    false
% 0.99/0.98  --res_prop_simpl_given                  true
% 0.99/0.98  --res_passive_queue_type                priority_queues
% 0.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/0.98  --res_passive_queues_freq               [15;5]
% 0.99/0.98  --res_forward_subs                      full
% 0.99/0.98  --res_backward_subs                     full
% 0.99/0.98  --res_forward_subs_resolution           true
% 0.99/0.98  --res_backward_subs_resolution          true
% 0.99/0.98  --res_orphan_elimination                true
% 0.99/0.98  --res_time_limit                        2.
% 0.99/0.98  --res_out_proof                         true
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Options
% 0.99/0.98  
% 0.99/0.98  --superposition_flag                    true
% 0.99/0.98  --sup_passive_queue_type                priority_queues
% 0.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.99/0.98  --demod_completeness_check              fast
% 0.99/0.98  --demod_use_ground                      true
% 0.99/0.98  --sup_to_prop_solver                    passive
% 0.99/0.98  --sup_prop_simpl_new                    true
% 0.99/0.98  --sup_prop_simpl_given                  true
% 0.99/0.98  --sup_fun_splitting                     false
% 0.99/0.98  --sup_smt_interval                      50000
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Simplification Setup
% 0.99/0.98  
% 0.99/0.98  --sup_indices_passive                   []
% 0.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_full_bw                           [BwDemod]
% 0.99/0.98  --sup_immed_triv                        [TrivRules]
% 0.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_immed_bw_main                     []
% 0.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  
% 0.99/0.98  ------ Combination Options
% 0.99/0.98  
% 0.99/0.98  --comb_res_mult                         3
% 0.99/0.98  --comb_sup_mult                         2
% 0.99/0.98  --comb_inst_mult                        10
% 0.99/0.98  
% 0.99/0.98  ------ Debug Options
% 0.99/0.98  
% 0.99/0.98  --dbg_backtrace                         false
% 0.99/0.98  --dbg_dump_prop_clauses                 false
% 0.99/0.98  --dbg_dump_prop_clauses_file            -
% 0.99/0.98  --dbg_out_stat                          false
% 0.99/0.98  ------ Parsing...
% 0.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/0.98  ------ Proving...
% 0.99/0.98  ------ Problem Properties 
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  clauses                                 26
% 0.99/0.98  conjectures                             18
% 0.99/0.98  EPR                                     12
% 0.99/0.98  Horn                                    21
% 0.99/0.98  unary                                   18
% 0.99/0.98  binary                                  1
% 0.99/0.98  lits                                    81
% 0.99/0.98  lits eq                                 0
% 0.99/0.98  fd_pure                                 0
% 0.99/0.98  fd_pseudo                               0
% 0.99/0.98  fd_cond                                 0
% 0.99/0.98  fd_pseudo_cond                          0
% 0.99/0.98  AC symbols                              0
% 0.99/0.98  
% 0.99/0.98  ------ Schedule dynamic 5 is on 
% 0.99/0.98  
% 0.99/0.98  ------ no equalities: superposition off 
% 0.99/0.98  
% 0.99/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  ------ 
% 0.99/0.98  Current options:
% 0.99/0.98  ------ 
% 0.99/0.98  
% 0.99/0.98  ------ Input Options
% 0.99/0.98  
% 0.99/0.98  --out_options                           all
% 0.99/0.98  --tptp_safe_out                         true
% 0.99/0.98  --problem_path                          ""
% 0.99/0.98  --include_path                          ""
% 0.99/0.98  --clausifier                            res/vclausify_rel
% 0.99/0.98  --clausifier_options                    --mode clausify
% 0.99/0.98  --stdin                                 false
% 0.99/0.98  --stats_out                             all
% 0.99/0.98  
% 0.99/0.98  ------ General Options
% 0.99/0.98  
% 0.99/0.98  --fof                                   false
% 0.99/0.98  --time_out_real                         305.
% 0.99/0.98  --time_out_virtual                      -1.
% 0.99/0.98  --symbol_type_check                     false
% 0.99/0.98  --clausify_out                          false
% 0.99/0.98  --sig_cnt_out                           false
% 0.99/0.98  --trig_cnt_out                          false
% 0.99/0.98  --trig_cnt_out_tolerance                1.
% 0.99/0.98  --trig_cnt_out_sk_spl                   false
% 0.99/0.98  --abstr_cl_out                          false
% 0.99/0.98  
% 0.99/0.98  ------ Global Options
% 0.99/0.98  
% 0.99/0.98  --schedule                              default
% 0.99/0.98  --add_important_lit                     false
% 0.99/0.98  --prop_solver_per_cl                    1000
% 0.99/0.98  --min_unsat_core                        false
% 0.99/0.98  --soft_assumptions                      false
% 0.99/0.98  --soft_lemma_size                       3
% 0.99/0.98  --prop_impl_unit_size                   0
% 0.99/0.98  --prop_impl_unit                        []
% 0.99/0.98  --share_sel_clauses                     true
% 0.99/0.98  --reset_solvers                         false
% 0.99/0.98  --bc_imp_inh                            [conj_cone]
% 0.99/0.98  --conj_cone_tolerance                   3.
% 0.99/0.98  --extra_neg_conj                        none
% 0.99/0.98  --large_theory_mode                     true
% 0.99/0.98  --prolific_symb_bound                   200
% 0.99/0.98  --lt_threshold                          2000
% 0.99/0.98  --clause_weak_htbl                      true
% 0.99/0.98  --gc_record_bc_elim                     false
% 0.99/0.98  
% 0.99/0.98  ------ Preprocessing Options
% 0.99/0.98  
% 0.99/0.98  --preprocessing_flag                    true
% 0.99/0.98  --time_out_prep_mult                    0.1
% 0.99/0.98  --splitting_mode                        input
% 0.99/0.98  --splitting_grd                         true
% 0.99/0.98  --splitting_cvd                         false
% 0.99/0.98  --splitting_cvd_svl                     false
% 0.99/0.98  --splitting_nvd                         32
% 0.99/0.98  --sub_typing                            true
% 0.99/0.98  --prep_gs_sim                           true
% 0.99/0.98  --prep_unflatten                        true
% 0.99/0.98  --prep_res_sim                          true
% 0.99/0.98  --prep_upred                            true
% 0.99/0.98  --prep_sem_filter                       exhaustive
% 0.99/0.98  --prep_sem_filter_out                   false
% 0.99/0.98  --pred_elim                             true
% 0.99/0.98  --res_sim_input                         true
% 0.99/0.98  --eq_ax_congr_red                       true
% 0.99/0.98  --pure_diseq_elim                       true
% 0.99/0.98  --brand_transform                       false
% 0.99/0.98  --non_eq_to_eq                          false
% 0.99/0.98  --prep_def_merge                        true
% 0.99/0.98  --prep_def_merge_prop_impl              false
% 0.99/0.98  --prep_def_merge_mbd                    true
% 0.99/0.98  --prep_def_merge_tr_red                 false
% 0.99/0.98  --prep_def_merge_tr_cl                  false
% 0.99/0.98  --smt_preprocessing                     true
% 0.99/0.98  --smt_ac_axioms                         fast
% 0.99/0.98  --preprocessed_out                      false
% 0.99/0.98  --preprocessed_stats                    false
% 0.99/0.98  
% 0.99/0.98  ------ Abstraction refinement Options
% 0.99/0.98  
% 0.99/0.98  --abstr_ref                             []
% 0.99/0.98  --abstr_ref_prep                        false
% 0.99/0.98  --abstr_ref_until_sat                   false
% 0.99/0.98  --abstr_ref_sig_restrict                funpre
% 0.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/0.98  --abstr_ref_under                       []
% 0.99/0.98  
% 0.99/0.98  ------ SAT Options
% 0.99/0.98  
% 0.99/0.98  --sat_mode                              false
% 0.99/0.98  --sat_fm_restart_options                ""
% 0.99/0.98  --sat_gr_def                            false
% 0.99/0.98  --sat_epr_types                         true
% 0.99/0.98  --sat_non_cyclic_types                  false
% 0.99/0.98  --sat_finite_models                     false
% 0.99/0.98  --sat_fm_lemmas                         false
% 0.99/0.98  --sat_fm_prep                           false
% 0.99/0.98  --sat_fm_uc_incr                        true
% 0.99/0.98  --sat_out_model                         small
% 0.99/0.98  --sat_out_clauses                       false
% 0.99/0.98  
% 0.99/0.98  ------ QBF Options
% 0.99/0.98  
% 0.99/0.98  --qbf_mode                              false
% 0.99/0.98  --qbf_elim_univ                         false
% 0.99/0.98  --qbf_dom_inst                          none
% 0.99/0.98  --qbf_dom_pre_inst                      false
% 0.99/0.98  --qbf_sk_in                             false
% 0.99/0.98  --qbf_pred_elim                         true
% 0.99/0.98  --qbf_split                             512
% 0.99/0.98  
% 0.99/0.98  ------ BMC1 Options
% 0.99/0.98  
% 0.99/0.98  --bmc1_incremental                      false
% 0.99/0.98  --bmc1_axioms                           reachable_all
% 0.99/0.98  --bmc1_min_bound                        0
% 0.99/0.98  --bmc1_max_bound                        -1
% 0.99/0.98  --bmc1_max_bound_default                -1
% 0.99/0.98  --bmc1_symbol_reachability              true
% 0.99/0.98  --bmc1_property_lemmas                  false
% 0.99/0.98  --bmc1_k_induction                      false
% 0.99/0.98  --bmc1_non_equiv_states                 false
% 0.99/0.98  --bmc1_deadlock                         false
% 0.99/0.98  --bmc1_ucm                              false
% 0.99/0.98  --bmc1_add_unsat_core                   none
% 0.99/0.98  --bmc1_unsat_core_children              false
% 0.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/0.98  --bmc1_out_stat                         full
% 0.99/0.98  --bmc1_ground_init                      false
% 0.99/0.98  --bmc1_pre_inst_next_state              false
% 0.99/0.98  --bmc1_pre_inst_state                   false
% 0.99/0.98  --bmc1_pre_inst_reach_state             false
% 0.99/0.98  --bmc1_out_unsat_core                   false
% 0.99/0.98  --bmc1_aig_witness_out                  false
% 0.99/0.98  --bmc1_verbose                          false
% 0.99/0.98  --bmc1_dump_clauses_tptp                false
% 0.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.99/0.98  --bmc1_dump_file                        -
% 0.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.99/0.98  --bmc1_ucm_extend_mode                  1
% 0.99/0.98  --bmc1_ucm_init_mode                    2
% 0.99/0.98  --bmc1_ucm_cone_mode                    none
% 0.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.99/0.98  --bmc1_ucm_relax_model                  4
% 0.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/0.98  --bmc1_ucm_layered_model                none
% 0.99/0.98  --bmc1_ucm_max_lemma_size               10
% 0.99/0.98  
% 0.99/0.98  ------ AIG Options
% 0.99/0.98  
% 0.99/0.98  --aig_mode                              false
% 0.99/0.98  
% 0.99/0.98  ------ Instantiation Options
% 0.99/0.98  
% 0.99/0.98  --instantiation_flag                    true
% 0.99/0.98  --inst_sos_flag                         false
% 0.99/0.98  --inst_sos_phase                        true
% 0.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/0.98  --inst_lit_sel_side                     none
% 0.99/0.98  --inst_solver_per_active                1400
% 0.99/0.98  --inst_solver_calls_frac                1.
% 0.99/0.98  --inst_passive_queue_type               priority_queues
% 0.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/0.98  --inst_passive_queues_freq              [25;2]
% 0.99/0.98  --inst_dismatching                      true
% 0.99/0.98  --inst_eager_unprocessed_to_passive     true
% 0.99/0.98  --inst_prop_sim_given                   true
% 0.99/0.98  --inst_prop_sim_new                     false
% 0.99/0.98  --inst_subs_new                         false
% 0.99/0.98  --inst_eq_res_simp                      false
% 0.99/0.98  --inst_subs_given                       false
% 0.99/0.98  --inst_orphan_elimination               true
% 0.99/0.98  --inst_learning_loop_flag               true
% 0.99/0.98  --inst_learning_start                   3000
% 0.99/0.98  --inst_learning_factor                  2
% 0.99/0.98  --inst_start_prop_sim_after_learn       3
% 0.99/0.98  --inst_sel_renew                        solver
% 0.99/0.98  --inst_lit_activity_flag                true
% 0.99/0.98  --inst_restr_to_given                   false
% 0.99/0.98  --inst_activity_threshold               500
% 0.99/0.98  --inst_out_proof                        true
% 0.99/0.98  
% 0.99/0.98  ------ Resolution Options
% 0.99/0.98  
% 0.99/0.98  --resolution_flag                       false
% 0.99/0.98  --res_lit_sel                           adaptive
% 0.99/0.98  --res_lit_sel_side                      none
% 0.99/0.98  --res_ordering                          kbo
% 0.99/0.98  --res_to_prop_solver                    active
% 0.99/0.98  --res_prop_simpl_new                    false
% 0.99/0.98  --res_prop_simpl_given                  true
% 0.99/0.98  --res_passive_queue_type                priority_queues
% 0.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/0.98  --res_passive_queues_freq               [15;5]
% 0.99/0.98  --res_forward_subs                      full
% 0.99/0.98  --res_backward_subs                     full
% 0.99/0.98  --res_forward_subs_resolution           true
% 0.99/0.98  --res_backward_subs_resolution          true
% 0.99/0.98  --res_orphan_elimination                true
% 0.99/0.98  --res_time_limit                        2.
% 0.99/0.98  --res_out_proof                         true
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Options
% 0.99/0.98  
% 0.99/0.98  --superposition_flag                    false
% 0.99/0.98  --sup_passive_queue_type                priority_queues
% 0.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.99/0.98  --demod_completeness_check              fast
% 0.99/0.98  --demod_use_ground                      true
% 0.99/0.98  --sup_to_prop_solver                    passive
% 0.99/0.98  --sup_prop_simpl_new                    true
% 0.99/0.98  --sup_prop_simpl_given                  true
% 0.99/0.98  --sup_fun_splitting                     false
% 0.99/0.98  --sup_smt_interval                      50000
% 0.99/0.98  
% 0.99/0.98  ------ Superposition Simplification Setup
% 0.99/0.98  
% 0.99/0.98  --sup_indices_passive                   []
% 0.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_full_bw                           [BwDemod]
% 0.99/0.98  --sup_immed_triv                        [TrivRules]
% 0.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_immed_bw_main                     []
% 0.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.98  
% 0.99/0.98  ------ Combination Options
% 0.99/0.98  
% 0.99/0.98  --comb_res_mult                         3
% 0.99/0.98  --comb_sup_mult                         2
% 0.99/0.98  --comb_inst_mult                        10
% 0.99/0.98  
% 0.99/0.98  ------ Debug Options
% 0.99/0.98  
% 0.99/0.98  --dbg_backtrace                         false
% 0.99/0.98  --dbg_dump_prop_clauses                 false
% 0.99/0.98  --dbg_dump_prop_clauses_file            -
% 0.99/0.98  --dbg_out_stat                          false
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  ------ Proving...
% 0.99/0.98  
% 0.99/0.98  
% 0.99/0.98  % SZS status Theorem for theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/0.98  
% 0.99/0.98  fof(f4,axiom,(
% 0.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f15,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.98    inference(ennf_transformation,[],[f4])).
% 0.99/0.98  
% 0.99/0.98  fof(f16,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(flattening,[],[f15])).
% 0.99/0.98  
% 0.99/0.98  fof(f23,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(nnf_transformation,[],[f16])).
% 0.99/0.98  
% 0.99/0.98  fof(f24,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(rectify,[],[f23])).
% 0.99/0.98  
% 0.99/0.98  fof(f25,plain,(
% 0.99/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f26,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 0.99/0.98  
% 0.99/0.98  fof(f38,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f26])).
% 0.99/0.98  
% 0.99/0.98  fof(f6,conjecture,(
% 0.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f7,negated_conjecture,(
% 0.99/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.99/0.98    inference(negated_conjecture,[],[f6])).
% 0.99/0.98  
% 0.99/0.98  fof(f19,plain,(
% 0.99/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & (v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5))) & m1_subset_1(X5,u1_struct_0(X2))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.99/0.98    inference(ennf_transformation,[],[f7])).
% 0.99/0.98  
% 0.99/0.98  fof(f20,plain,(
% 0.99/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.99/0.98    inference(flattening,[],[f19])).
% 0.99/0.98  
% 0.99/0.98  fof(f32,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),sK7) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,sK7) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f31,plain,(
% 0.99/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,sK6),X5) & v5_pre_topc(sK6,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f30,plain,(
% 0.99/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),sK5,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,sK5,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f29,plain,(
% 0.99/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(sK4,X1,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(sK4,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f28,plain,(
% 0.99/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,X0,sK3) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f27,plain,(
% 0.99/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,sK2,X1) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f33,plain,(
% 0.99/0.98    (((((~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,sK7) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f32,f31,f30,f29,f28,f27])).
% 0.99/0.98  
% 0.99/0.98  fof(f59,plain,(
% 0.99/0.98    v5_pre_topc(sK6,sK2,sK3)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f42,plain,(
% 0.99/0.98    ~v2_struct_0(sK2)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f43,plain,(
% 0.99/0.98    v2_pre_topc(sK2)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f44,plain,(
% 0.99/0.98    l1_pre_topc(sK2)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f45,plain,(
% 0.99/0.98    ~v2_struct_0(sK3)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f46,plain,(
% 0.99/0.98    v2_pre_topc(sK3)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f47,plain,(
% 0.99/0.98    l1_pre_topc(sK3)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f54,plain,(
% 0.99/0.98    v1_funct_1(sK6)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f55,plain,(
% 0.99/0.98    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f56,plain,(
% 0.99/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f3,axiom,(
% 0.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f8,plain,(
% 0.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/0.98    inference(pure_predicate_removal,[],[f3])).
% 0.99/0.98  
% 0.99/0.98  fof(f9,plain,(
% 0.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/0.98    inference(pure_predicate_removal,[],[f8])).
% 0.99/0.98  
% 0.99/0.98  fof(f13,plain,(
% 0.99/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.98    inference(ennf_transformation,[],[f9])).
% 0.99/0.98  
% 0.99/0.98  fof(f14,plain,(
% 0.99/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(flattening,[],[f13])).
% 0.99/0.98  
% 0.99/0.98  fof(f21,plain,(
% 0.99/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/0.98    introduced(choice_axiom,[])).
% 0.99/0.98  
% 0.99/0.98  fof(f22,plain,(
% 0.99/0.98    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).
% 0.99/0.98  
% 0.99/0.98  fof(f37,plain,(
% 0.99/0.98    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f22])).
% 0.99/0.98  
% 0.99/0.98  fof(f36,plain,(
% 0.99/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f22])).
% 0.99/0.98  
% 0.99/0.98  fof(f1,axiom,(
% 0.99/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f10,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.99/0.98    inference(ennf_transformation,[],[f1])).
% 0.99/0.98  
% 0.99/0.98  fof(f34,plain,(
% 0.99/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f10])).
% 0.99/0.98  
% 0.99/0.98  fof(f2,axiom,(
% 0.99/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f11,plain,(
% 0.99/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.99/0.98    inference(ennf_transformation,[],[f2])).
% 0.99/0.98  
% 0.99/0.98  fof(f12,plain,(
% 0.99/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.99/0.98    inference(flattening,[],[f11])).
% 0.99/0.98  
% 0.99/0.98  fof(f35,plain,(
% 0.99/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f12])).
% 0.99/0.98  
% 0.99/0.98  fof(f5,axiom,(
% 0.99/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/0.98  
% 0.99/0.98  fof(f17,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.98    inference(ennf_transformation,[],[f5])).
% 0.99/0.98  
% 0.99/0.98  fof(f18,plain,(
% 0.99/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.98    inference(flattening,[],[f17])).
% 0.99/0.98  
% 0.99/0.98  fof(f41,plain,(
% 0.99/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.98    inference(cnf_transformation,[],[f18])).
% 0.99/0.98  
% 0.99/0.98  fof(f61,plain,(
% 0.99/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.98    inference(equality_resolution,[],[f41])).
% 0.99/0.98  
% 0.99/0.98  fof(f60,plain,(
% 0.99/0.98    ~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f58,plain,(
% 0.99/0.98    r1_tmap_1(sK4,sK2,sK5,sK7)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f57,plain,(
% 0.99/0.98    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f53,plain,(
% 0.99/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f52,plain,(
% 0.99/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f51,plain,(
% 0.99/0.98    v1_funct_1(sK5)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f50,plain,(
% 0.99/0.98    l1_pre_topc(sK4)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f49,plain,(
% 0.99/0.98    v2_pre_topc(sK4)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  fof(f48,plain,(
% 0.99/0.98    ~v2_struct_0(sK4)),
% 0.99/0.98    inference(cnf_transformation,[],[f33])).
% 0.99/0.98  
% 0.99/0.98  cnf(c_6,plain,
% 0.99/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 0.99/0.98      | ~ v5_pre_topc(X2,X0,X1)
% 0.99/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 0.99/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.99/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.99/0.98      | v2_struct_0(X1)
% 0.99/0.98      | v2_struct_0(X0)
% 0.99/0.98      | ~ v2_pre_topc(X1)
% 0.99/0.98      | ~ v2_pre_topc(X0)
% 0.99/0.98      | ~ l1_pre_topc(X1)
% 0.99/0.98      | ~ l1_pre_topc(X0)
% 0.99/0.98      | ~ v1_funct_1(X2) ),
% 0.99/0.98      inference(cnf_transformation,[],[f38]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_9,negated_conjecture,
% 0.99/0.98      ( v5_pre_topc(sK6,sK2,sK3) ),
% 0.99/0.98      inference(cnf_transformation,[],[f59]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_339,plain,
% 0.99/0.98      ( r1_tmap_1(sK2,sK3,sK6,X0)
% 0.99/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.99/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.99/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.99/0.98      | v2_struct_0(sK2)
% 0.99/0.98      | v2_struct_0(sK3)
% 0.99/0.98      | ~ v2_pre_topc(sK2)
% 0.99/0.98      | ~ v2_pre_topc(sK3)
% 0.99/0.98      | ~ l1_pre_topc(sK2)
% 0.99/0.98      | ~ l1_pre_topc(sK3)
% 0.99/0.98      | ~ v1_funct_1(sK6) ),
% 0.99/0.98      inference(resolution,[status(thm)],[c_6,c_9]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_26,negated_conjecture,
% 0.99/0.98      ( ~ v2_struct_0(sK2) ),
% 0.99/0.98      inference(cnf_transformation,[],[f42]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_25,negated_conjecture,
% 0.99/0.98      ( v2_pre_topc(sK2) ),
% 0.99/0.98      inference(cnf_transformation,[],[f43]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_24,negated_conjecture,
% 0.99/0.98      ( l1_pre_topc(sK2) ),
% 0.99/0.98      inference(cnf_transformation,[],[f44]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_23,negated_conjecture,
% 0.99/0.98      ( ~ v2_struct_0(sK3) ),
% 0.99/0.98      inference(cnf_transformation,[],[f45]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_22,negated_conjecture,
% 0.99/0.98      ( v2_pre_topc(sK3) ),
% 0.99/0.98      inference(cnf_transformation,[],[f46]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_21,negated_conjecture,
% 0.99/0.98      ( l1_pre_topc(sK3) ),
% 0.99/0.98      inference(cnf_transformation,[],[f47]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_14,negated_conjecture,
% 0.99/0.98      ( v1_funct_1(sK6) ),
% 0.99/0.98      inference(cnf_transformation,[],[f54]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_13,negated_conjecture,
% 0.99/0.98      ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 0.99/0.98      inference(cnf_transformation,[],[f55]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_12,negated_conjecture,
% 0.99/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 0.99/0.98      inference(cnf_transformation,[],[f56]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_343,plain,
% 0.99/0.98      ( r1_tmap_1(sK2,sK3,sK6,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 0.99/0.98      inference(global_propositional_subsumption,
% 0.99/0.98                [status(thm)],
% 0.99/0.98                [c_339,c_26,c_25,c_24,c_23,c_22,c_21,c_14,c_13,c_12]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_518,plain,
% 0.99/0.98      ( r1_tmap_1(sK2,sK3,sK6,X0_51)
% 0.99/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
% 0.99/0.98      inference(subtyping,[status(esa)],[c_343]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_759,plain,
% 0.99/0.98      ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
% 0.99/0.98      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_518]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_2,plain,
% 0.99/0.98      ( v2_struct_0(X0)
% 0.99/0.98      | ~ v2_pre_topc(X0)
% 0.99/0.98      | ~ l1_pre_topc(X0)
% 0.99/0.98      | ~ v1_xboole_0(sK0(X0)) ),
% 0.99/0.98      inference(cnf_transformation,[],[f37]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_541,plain,
% 0.99/0.98      ( v2_struct_0(X0_50)
% 0.99/0.98      | ~ v2_pre_topc(X0_50)
% 0.99/0.98      | ~ l1_pre_topc(X0_50)
% 0.99/0.98      | ~ v1_xboole_0(sK0(X0_50)) ),
% 0.99/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_749,plain,
% 0.99/0.98      ( v2_struct_0(sK4)
% 0.99/0.98      | ~ v2_pre_topc(sK4)
% 0.99/0.98      | ~ l1_pre_topc(sK4)
% 0.99/0.98      | ~ v1_xboole_0(sK0(sK4)) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_541]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_3,plain,
% 0.99/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.99/0.98      | v2_struct_0(X0)
% 0.99/0.98      | ~ v2_pre_topc(X0)
% 0.99/0.98      | ~ l1_pre_topc(X0) ),
% 0.99/0.98      inference(cnf_transformation,[],[f36]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_540,plain,
% 0.99/0.98      ( m1_subset_1(sK0(X0_50),k1_zfmisc_1(u1_struct_0(X0_50)))
% 0.99/0.98      | v2_struct_0(X0_50)
% 0.99/0.98      | ~ v2_pre_topc(X0_50)
% 0.99/0.98      | ~ l1_pre_topc(X0_50) ),
% 0.99/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_743,plain,
% 0.99/0.98      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 0.99/0.98      | v2_struct_0(sK4)
% 0.99/0.98      | ~ v2_pre_topc(sK4)
% 0.99/0.98      | ~ l1_pre_topc(sK4) ),
% 0.99/0.98      inference(instantiation,[status(thm)],[c_540]) ).
% 0.99/0.98  
% 0.99/0.98  cnf(c_0,plain,
% 0.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/0.98      | ~ v1_xboole_0(X1)
% 0.99/0.98      | v1_xboole_0(X0) ),
% 0.99/0.98      inference(cnf_transformation,[],[f34]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_543,plain,
% 0.99/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 0.99/0.99      | ~ v1_xboole_0(X1_51)
% 0.99/0.99      | v1_xboole_0(X0_51) ),
% 0.99/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_689,plain,
% 0.99/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4)))
% 0.99/0.99      | v1_xboole_0(X0_51)
% 0.99/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 0.99/0.99      inference(instantiation,[status(thm)],[c_543]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_742,plain,
% 0.99/0.99      ( ~ m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 0.99/0.99      | ~ v1_xboole_0(u1_struct_0(sK4))
% 0.99/0.99      | v1_xboole_0(sK0(sK4)) ),
% 0.99/0.99      inference(instantiation,[status(thm)],[c_689]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_1,plain,
% 0.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 0.99/0.99      | ~ m1_subset_1(X3,X1)
% 0.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/0.99      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 0.99/0.99      | ~ v1_funct_1(X0)
% 0.99/0.99      | v1_xboole_0(X1) ),
% 0.99/0.99      inference(cnf_transformation,[],[f35]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_542,plain,
% 0.99/0.99      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 0.99/0.99      | ~ m1_subset_1(X3_51,X1_51)
% 0.99/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 0.99/0.99      | m1_subset_1(k3_funct_2(X1_51,X2_51,X0_51,X3_51),X2_51)
% 0.99/0.99      | ~ v1_funct_1(X0_51)
% 0.99/0.99      | v1_xboole_0(X1_51) ),
% 0.99/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_658,plain,
% 0.99/0.99      ( ~ v1_funct_2(X0_51,u1_struct_0(sK4),X1_51)
% 0.99/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_51)))
% 0.99/0.99      | m1_subset_1(k3_funct_2(u1_struct_0(sK4),X1_51,X0_51,sK7),X1_51)
% 0.99/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.99/0.99      | ~ v1_funct_1(X0_51)
% 0.99/0.99      | v1_xboole_0(u1_struct_0(sK4)) ),
% 0.99/0.99      inference(instantiation,[status(thm)],[c_542]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_738,plain,
% 0.99/0.99      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 0.99/0.99      | m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
% 0.99/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.99/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 0.99/0.99      | ~ v1_funct_1(sK5)
% 0.99/0.99      | v1_xboole_0(u1_struct_0(sK4)) ),
% 0.99/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_7,plain,
% 0.99/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 0.99/0.99      | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 0.99/0.99      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
% 0.99/0.99      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 0.99/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 0.99/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.99/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 0.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.99/0.99      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
% 0.99/0.99      | v2_struct_0(X4)
% 0.99/0.99      | v2_struct_0(X0)
% 0.99/0.99      | v2_struct_0(X1)
% 0.99/0.99      | ~ v2_pre_topc(X4)
% 0.99/0.99      | ~ v2_pre_topc(X0)
% 0.99/0.99      | ~ v2_pre_topc(X1)
% 0.99/0.99      | ~ l1_pre_topc(X4)
% 0.99/0.99      | ~ l1_pre_topc(X0)
% 0.99/0.99      | ~ l1_pre_topc(X1)
% 0.99/0.99      | ~ v1_funct_1(X5)
% 0.99/0.99      | ~ v1_funct_1(X2) ),
% 0.99/0.99      inference(cnf_transformation,[],[f61]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_539,plain,
% 0.99/0.99      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
% 0.99/0.99      | ~ r1_tmap_1(X1_50,X2_50,X2_51,k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,X1_51))
% 0.99/0.99      | r1_tmap_1(X0_50,X2_50,k1_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),u1_struct_0(X1_50),u1_struct_0(X2_50),X0_51,X2_51),X1_51)
% 0.99/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 0.99/0.99      | ~ v1_funct_2(X2_51,u1_struct_0(X1_50),u1_struct_0(X2_50))
% 0.99/0.99      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 0.99/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 0.99/0.99      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X2_50))))
% 0.99/0.99      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,X1_51),u1_struct_0(X1_50))
% 0.99/0.99      | v2_struct_0(X1_50)
% 0.99/0.99      | v2_struct_0(X0_50)
% 0.99/0.99      | v2_struct_0(X2_50)
% 0.99/0.99      | ~ v2_pre_topc(X1_50)
% 0.99/0.99      | ~ v2_pre_topc(X0_50)
% 0.99/0.99      | ~ v2_pre_topc(X2_50)
% 0.99/0.99      | ~ l1_pre_topc(X1_50)
% 0.99/0.99      | ~ l1_pre_topc(X0_50)
% 0.99/0.99      | ~ l1_pre_topc(X2_50)
% 0.99/0.99      | ~ v1_funct_1(X2_51)
% 0.99/0.99      | ~ v1_funct_1(X0_51) ),
% 0.99/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_684,plain,
% 0.99/0.99      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_50),X1_51,sK7))
% 0.99/0.99      | ~ r1_tmap_1(sK4,X0_50,X1_51,sK7)
% 0.99/0.99      | r1_tmap_1(sK4,X1_50,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50),X1_51,X0_51),sK7)
% 0.99/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 0.99/0.99      | ~ v1_funct_2(X1_51,u1_struct_0(sK4),u1_struct_0(X0_50))
% 0.99/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 0.99/0.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_50))))
% 0.99/0.99      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_50),X1_51,sK7),u1_struct_0(X0_50))
% 0.99/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.99/0.99      | v2_struct_0(X1_50)
% 0.99/0.99      | v2_struct_0(X0_50)
% 0.99/0.99      | v2_struct_0(sK4)
% 0.99/0.99      | ~ v2_pre_topc(X1_50)
% 0.99/0.99      | ~ v2_pre_topc(X0_50)
% 0.99/0.99      | ~ v2_pre_topc(sK4)
% 0.99/0.99      | ~ l1_pre_topc(X1_50)
% 0.99/0.99      | ~ l1_pre_topc(X0_50)
% 0.99/0.99      | ~ l1_pre_topc(sK4)
% 0.99/0.99      | ~ v1_funct_1(X1_51)
% 0.99/0.99      | ~ v1_funct_1(X0_51) ),
% 0.99/0.99      inference(instantiation,[status(thm)],[c_539]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_710,plain,
% 0.99/0.99      ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
% 0.99/0.99      | ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 0.99/0.99      | r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
% 0.99/0.99      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.99/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 0.99/0.99      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
% 0.99/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.99/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.99/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 0.99/0.99      | v2_struct_0(sK2)
% 0.99/0.99      | v2_struct_0(sK3)
% 0.99/0.99      | v2_struct_0(sK4)
% 0.99/0.99      | ~ v2_pre_topc(sK2)
% 0.99/0.99      | ~ v2_pre_topc(sK3)
% 0.99/0.99      | ~ v2_pre_topc(sK4)
% 0.99/0.99      | ~ l1_pre_topc(sK2)
% 0.99/0.99      | ~ l1_pre_topc(sK3)
% 0.99/0.99      | ~ l1_pre_topc(sK4)
% 0.99/0.99      | ~ v1_funct_1(sK6)
% 0.99/0.99      | ~ v1_funct_1(sK5) ),
% 0.99/0.99      inference(instantiation,[status(thm)],[c_684]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_8,negated_conjecture,
% 0.99/0.99      ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
% 0.99/0.99      inference(cnf_transformation,[],[f60]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_10,negated_conjecture,
% 0.99/0.99      ( r1_tmap_1(sK4,sK2,sK5,sK7) ),
% 0.99/0.99      inference(cnf_transformation,[],[f58]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_11,negated_conjecture,
% 0.99/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 0.99/0.99      inference(cnf_transformation,[],[f57]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_15,negated_conjecture,
% 0.99/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 0.99/0.99      inference(cnf_transformation,[],[f53]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_16,negated_conjecture,
% 0.99/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 0.99/0.99      inference(cnf_transformation,[],[f52]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_17,negated_conjecture,
% 0.99/0.99      ( v1_funct_1(sK5) ),
% 0.99/0.99      inference(cnf_transformation,[],[f51]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_18,negated_conjecture,
% 0.99/0.99      ( l1_pre_topc(sK4) ),
% 0.99/0.99      inference(cnf_transformation,[],[f50]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_19,negated_conjecture,
% 0.99/0.99      ( v2_pre_topc(sK4) ),
% 0.99/0.99      inference(cnf_transformation,[],[f49]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(c_20,negated_conjecture,
% 0.99/0.99      ( ~ v2_struct_0(sK4) ),
% 0.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 0.99/0.99  
% 0.99/0.99  cnf(contradiction,plain,
% 0.99/0.99      ( $false ),
% 0.99/0.99      inference(minisat,
% 0.99/0.99                [status(thm)],
% 0.99/0.99                [c_759,c_749,c_743,c_742,c_738,c_710,c_8,c_10,c_11,c_12,
% 0.99/0.99                 c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,
% 0.99/0.99                 c_24,c_25,c_26]) ).
% 0.99/0.99  
% 0.99/0.99  
% 0.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/0.99  
% 0.99/0.99  ------                               Statistics
% 0.99/0.99  
% 0.99/0.99  ------ General
% 0.99/0.99  
% 0.99/0.99  abstr_ref_over_cycles:                  0
% 0.99/0.99  abstr_ref_under_cycles:                 0
% 0.99/0.99  gc_basic_clause_elim:                   0
% 0.99/0.99  forced_gc_time:                         0
% 0.99/0.99  parsing_time:                           0.011
% 0.99/0.99  unif_index_cands_time:                  0.
% 0.99/0.99  unif_index_add_time:                    0.
% 0.99/0.99  orderings_time:                         0.
% 0.99/0.99  out_proof_time:                         0.013
% 0.99/0.99  total_time:                             0.071
% 0.99/0.99  num_of_symbols:                         55
% 0.99/0.99  num_of_terms:                           1124
% 0.99/0.99  
% 0.99/0.99  ------ Preprocessing
% 0.99/0.99  
% 0.99/0.99  num_of_splits:                          0
% 0.99/0.99  num_of_split_atoms:                     0
% 0.99/0.99  num_of_reused_defs:                     0
% 0.99/0.99  num_eq_ax_congr_red:                    0
% 0.99/0.99  num_of_sem_filtered_clauses:            0
% 0.99/0.99  num_of_subtypes:                        2
% 0.99/0.99  monotx_restored_types:                  0
% 0.99/0.99  sat_num_of_epr_types:                   0
% 0.99/0.99  sat_num_of_non_cyclic_types:            0
% 0.99/0.99  sat_guarded_non_collapsed_types:        0
% 0.99/0.99  num_pure_diseq_elim:                    0
% 0.99/0.99  simp_replaced_by:                       0
% 0.99/0.99  res_preprocessed:                       53
% 0.99/0.99  prep_upred:                             0
% 0.99/0.99  prep_unflattend:                        0
% 0.99/0.99  smt_new_axioms:                         0
% 0.99/0.99  pred_elim_cands:                        8
% 0.99/0.99  pred_elim:                              1
% 0.99/0.99  pred_elim_cl:                           1
% 0.99/0.99  pred_elim_cycles:                       3
% 0.99/0.99  merged_defs:                            0
% 0.99/0.99  merged_defs_ncl:                        0
% 0.99/0.99  bin_hyper_res:                          0
% 0.99/0.99  prep_cycles:                            2
% 0.99/0.99  pred_elim_time:                         0.003
% 0.99/0.99  splitting_time:                         0.
% 0.99/0.99  sem_filter_time:                        0.
% 0.99/0.99  monotx_time:                            0.
% 0.99/0.99  subtype_inf_time:                       0.
% 0.99/0.99  
% 0.99/0.99  ------ Problem properties
% 0.99/0.99  
% 0.99/0.99  clauses:                                26
% 0.99/0.99  conjectures:                            18
% 0.99/0.99  epr:                                    12
% 0.99/0.99  horn:                                   21
% 0.99/0.99  ground:                                 18
% 0.99/0.99  unary:                                  18
% 0.99/0.99  binary:                                 1
% 0.99/0.99  lits:                                   81
% 0.99/0.99  lits_eq:                                0
% 0.99/0.99  fd_pure:                                0
% 0.99/0.99  fd_pseudo:                              0
% 0.99/0.99  fd_cond:                                0
% 0.99/0.99  fd_pseudo_cond:                         0
% 0.99/0.99  ac_symbols:                             0
% 0.99/0.99  
% 0.99/0.99  ------ Propositional Solver
% 0.99/0.99  
% 0.99/0.99  prop_solver_calls:                      15
% 0.99/0.99  prop_fast_solver_calls:                 379
% 0.99/0.99  smt_solver_calls:                       0
% 0.99/0.99  smt_fast_solver_calls:                  0
% 0.99/0.99  prop_num_of_clauses:                    184
% 0.99/0.99  prop_preprocess_simplified:             1260
% 0.99/0.99  prop_fo_subsumed:                       9
% 0.99/0.99  prop_solver_time:                       0.
% 0.99/0.99  smt_solver_time:                        0.
% 0.99/0.99  smt_fast_solver_time:                   0.
% 0.99/0.99  prop_fast_solver_time:                  0.
% 0.99/0.99  prop_unsat_core_time:                   0.
% 0.99/0.99  
% 0.99/0.99  ------ QBF
% 0.99/0.99  
% 0.99/0.99  qbf_q_res:                              0
% 0.99/0.99  qbf_num_tautologies:                    0
% 0.99/0.99  qbf_prep_cycles:                        0
% 0.99/0.99  
% 0.99/0.99  ------ BMC1
% 0.99/0.99  
% 0.99/0.99  bmc1_current_bound:                     -1
% 0.99/0.99  bmc1_last_solved_bound:                 -1
% 0.99/0.99  bmc1_unsat_core_size:                   -1
% 0.99/0.99  bmc1_unsat_core_parents_size:           -1
% 0.99/0.99  bmc1_merge_next_fun:                    0
% 0.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.99/0.99  
% 0.99/0.99  ------ Instantiation
% 0.99/0.99  
% 0.99/0.99  inst_num_of_clauses:                    49
% 0.99/0.99  inst_num_in_passive:                    2
% 0.99/0.99  inst_num_in_active:                     46
% 0.99/0.99  inst_num_in_unprocessed:                0
% 0.99/0.99  inst_num_of_loops:                      61
% 0.99/0.99  inst_num_of_learning_restarts:          0
% 0.99/0.99  inst_num_moves_active_passive:          9
% 0.99/0.99  inst_lit_activity:                      0
% 0.99/0.99  inst_lit_activity_moves:                0
% 0.99/0.99  inst_num_tautologies:                   0
% 0.99/0.99  inst_num_prop_implied:                  0
% 0.99/0.99  inst_num_existing_simplified:           0
% 0.99/0.99  inst_num_eq_res_simplified:             0
% 0.99/0.99  inst_num_child_elim:                    0
% 0.99/0.99  inst_num_of_dismatching_blockings:      1
% 0.99/0.99  inst_num_of_non_proper_insts:           24
% 0.99/0.99  inst_num_of_duplicates:                 0
% 0.99/0.99  inst_inst_num_from_inst_to_res:         0
% 0.99/0.99  inst_dismatching_checking_time:         0.
% 0.99/0.99  
% 0.99/0.99  ------ Resolution
% 0.99/0.99  
% 0.99/0.99  res_num_of_clauses:                     0
% 0.99/0.99  res_num_in_passive:                     0
% 0.99/0.99  res_num_in_active:                      0
% 0.99/0.99  res_num_of_loops:                       55
% 0.99/0.99  res_forward_subset_subsumed:            0
% 0.99/0.99  res_backward_subset_subsumed:           0
% 0.99/0.99  res_forward_subsumed:                   0
% 0.99/0.99  res_backward_subsumed:                  0
% 0.99/0.99  res_forward_subsumption_resolution:     0
% 0.99/0.99  res_backward_subsumption_resolution:    0
% 0.99/0.99  res_clause_to_clause_subsumption:       0
% 0.99/0.99  res_orphan_elimination:                 0
% 0.99/0.99  res_tautology_del:                      0
% 0.99/0.99  res_num_eq_res_simplified:              0
% 0.99/0.99  res_num_sel_changes:                    0
% 0.99/0.99  res_moves_from_active_to_pass:          0
% 0.99/0.99  
% 0.99/0.99  ------ Superposition
% 0.99/0.99  
% 0.99/0.99  sup_time_total:                         0.
% 0.99/0.99  sup_time_generating:                    0.
% 0.99/0.99  sup_time_sim_full:                      0.
% 0.99/0.99  sup_time_sim_immed:                     0.
% 0.99/0.99  
% 0.99/0.99  sup_num_of_clauses:                     0
% 0.99/0.99  sup_num_in_active:                      0
% 0.99/0.99  sup_num_in_passive:                     0
% 0.99/0.99  sup_num_of_loops:                       0
% 0.99/0.99  sup_fw_superposition:                   0
% 0.99/0.99  sup_bw_superposition:                   0
% 0.99/0.99  sup_immediate_simplified:               0
% 0.99/0.99  sup_given_eliminated:                   0
% 0.99/0.99  comparisons_done:                       0
% 0.99/0.99  comparisons_avoided:                    0
% 0.99/0.99  
% 0.99/0.99  ------ Simplifications
% 0.99/0.99  
% 0.99/0.99  
% 0.99/0.99  sim_fw_subset_subsumed:                 0
% 0.99/0.99  sim_bw_subset_subsumed:                 0
% 0.99/0.99  sim_fw_subsumed:                        0
% 0.99/0.99  sim_bw_subsumed:                        0
% 0.99/0.99  sim_fw_subsumption_res:                 0
% 0.99/0.99  sim_bw_subsumption_res:                 0
% 0.99/0.99  sim_tautology_del:                      0
% 0.99/0.99  sim_eq_tautology_del:                   0
% 0.99/0.99  sim_eq_res_simp:                        0
% 0.99/0.99  sim_fw_demodulated:                     0
% 0.99/0.99  sim_bw_demodulated:                     0
% 0.99/0.99  sim_light_normalised:                   0
% 0.99/0.99  sim_joinable_taut:                      0
% 0.99/0.99  sim_joinable_simp:                      0
% 0.99/0.99  sim_ac_normalised:                      0
% 0.99/0.99  sim_smt_subsumption:                    0
% 0.99/0.99  
%------------------------------------------------------------------------------
