%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:17 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 425 expanded)
%              Number of clauses        :   46 (  55 expanded)
%              Number of leaves         :   16 ( 205 expanded)
%              Depth                    :   12
%              Number of atoms          :  766 (7075 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f36,f35,f34,f33,f32,f31])).

fof(f65,plain,(
    v5_pre_topc(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
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
    inference(equality_resolution,[],[f47])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f44])).

cnf(c_11,negated_conjecture,
    ( v5_pre_topc(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_390,plain,
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
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_394,plain,
    ( r1_tmap_1(sK2,sK3,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_28,c_27,c_26,c_25,c_24,c_23,c_16,c_15,c_14])).

cnf(c_569,plain,
    ( r1_tmap_1(sK2,sK3,sK6,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_787,plain,
    ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0_53)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_784,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(k1_connsp_2(sK4,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_9,plain,
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
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_591,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
    | ~ r1_tmap_1(X1_52,X2_52,X2_53,k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,X1_53))
    | r1_tmap_1(X0_52,X2_52,k1_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),u1_struct_0(X1_52),u1_struct_0(X2_52),X0_53,X2_53),X1_53)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X2_53,u1_struct_0(X1_52),u1_struct_0(X2_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X2_52))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,X1_53),u1_struct_0(X1_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v1_funct_1(X2_53)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_740,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,X0_53,k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_52),X1_53,sK7))
    | ~ r1_tmap_1(sK4,X0_52,X1_53,sK7)
    | r1_tmap_1(sK4,X1_52,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0_52),u1_struct_0(X0_52),u1_struct_0(X1_52),X1_53,X0_53),sK7)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_52),X1_53,sK7),u1_struct_0(X0_52))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_759,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),X0_53,sK7))
    | ~ r1_tmap_1(sK4,sK2,X0_53,sK7)
    | r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X0_53,sK6),sK7)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),X0_53,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_761,plain,
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
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_593,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X3_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | m1_subset_1(k3_funct_2(X1_53,X2_53,X0_53,X3_53),X2_53)
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_719,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_53)))
    | m1_subset_1(k3_funct_2(u1_struct_0(sK4),X1_53,X0_53,sK7),X1_53)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_750,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(k1_connsp_2(X0_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
    | v2_struct_0(X0_52)
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_716,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_connsp_2(X1,X0)) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v1_xboole_0(k1_connsp_2(X0_52,X0_53)) ),
    inference(subtyping,[status(esa)],[c_282])).

cnf(c_713,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(k1_connsp_2(sK4,sK7)) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_787,c_784,c_761,c_750,c_716,c_713,c_10,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.31  % Computer   : n021.cluster.edu
% 0.09/0.31  % Model      : x86_64 x86_64
% 0.09/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.31  % Memory     : 8042.1875MB
% 0.09/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.31  % CPULimit   : 60
% 0.09/0.31  % WCLimit    : 600
% 0.09/0.31  % DateTime   : Tue Dec  1 18:02:04 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.09/0.31  % Running in FOF mode
% 0.97/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.97/0.97  
% 0.97/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.97/0.97  
% 0.97/0.97  ------  iProver source info
% 0.97/0.97  
% 0.97/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.97/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.97/0.97  git: non_committed_changes: false
% 0.97/0.97  git: last_make_outside_of_git: false
% 0.97/0.97  
% 0.97/0.97  ------ 
% 0.97/0.97  
% 0.97/0.97  ------ Input Options
% 0.97/0.97  
% 0.97/0.97  --out_options                           all
% 0.97/0.97  --tptp_safe_out                         true
% 0.97/0.97  --problem_path                          ""
% 0.97/0.97  --include_path                          ""
% 0.97/0.97  --clausifier                            res/vclausify_rel
% 0.97/0.97  --clausifier_options                    --mode clausify
% 0.97/0.97  --stdin                                 false
% 0.97/0.97  --stats_out                             all
% 0.97/0.97  
% 0.97/0.97  ------ General Options
% 0.97/0.97  
% 0.97/0.97  --fof                                   false
% 0.97/0.97  --time_out_real                         305.
% 0.97/0.97  --time_out_virtual                      -1.
% 0.97/0.97  --symbol_type_check                     false
% 0.97/0.97  --clausify_out                          false
% 0.97/0.97  --sig_cnt_out                           false
% 0.97/0.97  --trig_cnt_out                          false
% 0.97/0.97  --trig_cnt_out_tolerance                1.
% 0.97/0.97  --trig_cnt_out_sk_spl                   false
% 0.97/0.97  --abstr_cl_out                          false
% 0.97/0.97  
% 0.97/0.97  ------ Global Options
% 0.97/0.97  
% 0.97/0.97  --schedule                              default
% 0.97/0.97  --add_important_lit                     false
% 0.97/0.97  --prop_solver_per_cl                    1000
% 0.97/0.97  --min_unsat_core                        false
% 0.97/0.97  --soft_assumptions                      false
% 0.97/0.97  --soft_lemma_size                       3
% 0.97/0.97  --prop_impl_unit_size                   0
% 0.97/0.97  --prop_impl_unit                        []
% 0.97/0.97  --share_sel_clauses                     true
% 0.97/0.97  --reset_solvers                         false
% 0.97/0.97  --bc_imp_inh                            [conj_cone]
% 0.97/0.97  --conj_cone_tolerance                   3.
% 0.97/0.97  --extra_neg_conj                        none
% 0.97/0.97  --large_theory_mode                     true
% 0.97/0.97  --prolific_symb_bound                   200
% 0.97/0.97  --lt_threshold                          2000
% 0.97/0.97  --clause_weak_htbl                      true
% 0.97/0.97  --gc_record_bc_elim                     false
% 0.97/0.97  
% 0.97/0.97  ------ Preprocessing Options
% 0.97/0.97  
% 0.97/0.97  --preprocessing_flag                    true
% 0.97/0.97  --time_out_prep_mult                    0.1
% 0.97/0.97  --splitting_mode                        input
% 0.97/0.97  --splitting_grd                         true
% 0.97/0.97  --splitting_cvd                         false
% 0.97/0.97  --splitting_cvd_svl                     false
% 0.97/0.97  --splitting_nvd                         32
% 0.97/0.97  --sub_typing                            true
% 0.97/0.97  --prep_gs_sim                           true
% 0.97/0.97  --prep_unflatten                        true
% 0.97/0.97  --prep_res_sim                          true
% 0.97/0.97  --prep_upred                            true
% 0.97/0.97  --prep_sem_filter                       exhaustive
% 0.97/0.97  --prep_sem_filter_out                   false
% 0.97/0.97  --pred_elim                             true
% 0.97/0.97  --res_sim_input                         true
% 0.97/0.97  --eq_ax_congr_red                       true
% 0.97/0.97  --pure_diseq_elim                       true
% 0.97/0.97  --brand_transform                       false
% 0.97/0.97  --non_eq_to_eq                          false
% 0.97/0.97  --prep_def_merge                        true
% 0.97/0.97  --prep_def_merge_prop_impl              false
% 0.97/0.97  --prep_def_merge_mbd                    true
% 0.97/0.97  --prep_def_merge_tr_red                 false
% 0.97/0.97  --prep_def_merge_tr_cl                  false
% 0.97/0.97  --smt_preprocessing                     true
% 0.97/0.97  --smt_ac_axioms                         fast
% 0.97/0.97  --preprocessed_out                      false
% 0.97/0.97  --preprocessed_stats                    false
% 0.97/0.97  
% 0.97/0.97  ------ Abstraction refinement Options
% 0.97/0.97  
% 0.97/0.97  --abstr_ref                             []
% 0.97/0.97  --abstr_ref_prep                        false
% 0.97/0.97  --abstr_ref_until_sat                   false
% 0.97/0.97  --abstr_ref_sig_restrict                funpre
% 0.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.97/0.97  --abstr_ref_under                       []
% 0.97/0.97  
% 0.97/0.97  ------ SAT Options
% 0.97/0.97  
% 0.97/0.97  --sat_mode                              false
% 0.97/0.97  --sat_fm_restart_options                ""
% 0.97/0.97  --sat_gr_def                            false
% 0.97/0.97  --sat_epr_types                         true
% 0.97/0.97  --sat_non_cyclic_types                  false
% 0.97/0.97  --sat_finite_models                     false
% 0.97/0.97  --sat_fm_lemmas                         false
% 0.97/0.97  --sat_fm_prep                           false
% 0.97/0.97  --sat_fm_uc_incr                        true
% 0.97/0.97  --sat_out_model                         small
% 0.97/0.97  --sat_out_clauses                       false
% 0.97/0.97  
% 0.97/0.97  ------ QBF Options
% 0.97/0.97  
% 0.97/0.97  --qbf_mode                              false
% 0.97/0.97  --qbf_elim_univ                         false
% 0.97/0.97  --qbf_dom_inst                          none
% 0.97/0.97  --qbf_dom_pre_inst                      false
% 0.97/0.97  --qbf_sk_in                             false
% 0.97/0.97  --qbf_pred_elim                         true
% 0.97/0.97  --qbf_split                             512
% 0.97/0.97  
% 0.97/0.97  ------ BMC1 Options
% 0.97/0.97  
% 0.97/0.97  --bmc1_incremental                      false
% 0.97/0.97  --bmc1_axioms                           reachable_all
% 0.97/0.97  --bmc1_min_bound                        0
% 0.97/0.97  --bmc1_max_bound                        -1
% 0.97/0.97  --bmc1_max_bound_default                -1
% 0.97/0.97  --bmc1_symbol_reachability              true
% 0.97/0.97  --bmc1_property_lemmas                  false
% 0.97/0.97  --bmc1_k_induction                      false
% 0.97/0.97  --bmc1_non_equiv_states                 false
% 0.97/0.97  --bmc1_deadlock                         false
% 0.97/0.97  --bmc1_ucm                              false
% 0.97/0.97  --bmc1_add_unsat_core                   none
% 0.97/0.97  --bmc1_unsat_core_children              false
% 0.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.97/0.97  --bmc1_out_stat                         full
% 0.97/0.97  --bmc1_ground_init                      false
% 0.97/0.97  --bmc1_pre_inst_next_state              false
% 0.97/0.97  --bmc1_pre_inst_state                   false
% 0.97/0.97  --bmc1_pre_inst_reach_state             false
% 0.97/0.97  --bmc1_out_unsat_core                   false
% 0.97/0.97  --bmc1_aig_witness_out                  false
% 0.97/0.97  --bmc1_verbose                          false
% 0.97/0.97  --bmc1_dump_clauses_tptp                false
% 0.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.97/0.97  --bmc1_dump_file                        -
% 0.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.97/0.97  --bmc1_ucm_extend_mode                  1
% 0.97/0.97  --bmc1_ucm_init_mode                    2
% 0.97/0.97  --bmc1_ucm_cone_mode                    none
% 0.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.97/0.97  --bmc1_ucm_relax_model                  4
% 0.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.97/0.97  --bmc1_ucm_layered_model                none
% 0.97/0.97  --bmc1_ucm_max_lemma_size               10
% 0.97/0.97  
% 0.97/0.97  ------ AIG Options
% 0.97/0.97  
% 0.97/0.97  --aig_mode                              false
% 0.97/0.97  
% 0.97/0.97  ------ Instantiation Options
% 0.97/0.97  
% 0.97/0.97  --instantiation_flag                    true
% 0.97/0.97  --inst_sos_flag                         false
% 0.97/0.97  --inst_sos_phase                        true
% 0.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.97/0.97  --inst_lit_sel_side                     num_symb
% 0.97/0.97  --inst_solver_per_active                1400
% 0.97/0.97  --inst_solver_calls_frac                1.
% 0.97/0.97  --inst_passive_queue_type               priority_queues
% 0.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.97/0.97  --inst_passive_queues_freq              [25;2]
% 0.97/0.97  --inst_dismatching                      true
% 0.97/0.97  --inst_eager_unprocessed_to_passive     true
% 0.97/0.97  --inst_prop_sim_given                   true
% 0.97/0.97  --inst_prop_sim_new                     false
% 0.97/0.97  --inst_subs_new                         false
% 0.97/0.97  --inst_eq_res_simp                      false
% 0.97/0.97  --inst_subs_given                       false
% 0.97/0.97  --inst_orphan_elimination               true
% 0.97/0.97  --inst_learning_loop_flag               true
% 0.97/0.97  --inst_learning_start                   3000
% 0.97/0.97  --inst_learning_factor                  2
% 0.97/0.97  --inst_start_prop_sim_after_learn       3
% 0.97/0.97  --inst_sel_renew                        solver
% 0.97/0.97  --inst_lit_activity_flag                true
% 0.97/0.97  --inst_restr_to_given                   false
% 0.97/0.97  --inst_activity_threshold               500
% 0.97/0.97  --inst_out_proof                        true
% 0.97/0.97  
% 0.97/0.97  ------ Resolution Options
% 0.97/0.97  
% 0.97/0.97  --resolution_flag                       true
% 0.97/0.97  --res_lit_sel                           adaptive
% 0.97/0.97  --res_lit_sel_side                      none
% 0.97/0.97  --res_ordering                          kbo
% 0.97/0.97  --res_to_prop_solver                    active
% 0.97/0.97  --res_prop_simpl_new                    false
% 0.97/0.97  --res_prop_simpl_given                  true
% 0.97/0.97  --res_passive_queue_type                priority_queues
% 0.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.97/0.97  --res_passive_queues_freq               [15;5]
% 0.97/0.97  --res_forward_subs                      full
% 0.97/0.97  --res_backward_subs                     full
% 0.97/0.97  --res_forward_subs_resolution           true
% 0.97/0.97  --res_backward_subs_resolution          true
% 0.97/0.97  --res_orphan_elimination                true
% 0.97/0.97  --res_time_limit                        2.
% 0.97/0.97  --res_out_proof                         true
% 0.97/0.97  
% 0.97/0.97  ------ Superposition Options
% 0.97/0.97  
% 0.97/0.97  --superposition_flag                    true
% 0.97/0.97  --sup_passive_queue_type                priority_queues
% 0.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.97/0.97  --demod_completeness_check              fast
% 0.97/0.97  --demod_use_ground                      true
% 0.97/0.97  --sup_to_prop_solver                    passive
% 0.97/0.97  --sup_prop_simpl_new                    true
% 0.97/0.97  --sup_prop_simpl_given                  true
% 0.97/0.97  --sup_fun_splitting                     false
% 0.97/0.97  --sup_smt_interval                      50000
% 0.97/0.97  
% 0.97/0.97  ------ Superposition Simplification Setup
% 0.97/0.97  
% 0.97/0.97  --sup_indices_passive                   []
% 0.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.97  --sup_full_bw                           [BwDemod]
% 0.97/0.97  --sup_immed_triv                        [TrivRules]
% 0.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.97  --sup_immed_bw_main                     []
% 0.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.97  
% 0.97/0.97  ------ Combination Options
% 0.97/0.97  
% 0.97/0.97  --comb_res_mult                         3
% 0.97/0.97  --comb_sup_mult                         2
% 0.97/0.97  --comb_inst_mult                        10
% 0.97/0.97  
% 0.97/0.97  ------ Debug Options
% 0.97/0.97  
% 0.97/0.97  --dbg_backtrace                         false
% 0.97/0.97  --dbg_dump_prop_clauses                 false
% 0.97/0.97  --dbg_dump_prop_clauses_file            -
% 0.97/0.97  --dbg_out_stat                          false
% 0.97/0.97  ------ Parsing...
% 0.97/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.97/0.97  
% 0.97/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.97/0.97  
% 0.97/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.97/0.97  ------ Proving...
% 0.97/0.97  ------ Problem Properties 
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  clauses                                 26
% 0.97/0.97  conjectures                             18
% 0.97/0.97  EPR                                     12
% 0.97/0.97  Horn                                    21
% 0.97/0.97  unary                                   18
% 0.97/0.97  binary                                  1
% 0.97/0.97  lits                                    83
% 0.97/0.97  lits eq                                 0
% 0.97/0.97  fd_pure                                 0
% 0.97/0.97  fd_pseudo                               0
% 0.97/0.97  fd_cond                                 0
% 0.97/0.97  fd_pseudo_cond                          0
% 0.97/0.97  AC symbols                              0
% 0.97/0.97  
% 0.97/0.97  ------ Schedule dynamic 5 is on 
% 0.97/0.97  
% 0.97/0.97  ------ no equalities: superposition off 
% 0.97/0.97  
% 0.97/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  ------ 
% 0.97/0.97  Current options:
% 0.97/0.97  ------ 
% 0.97/0.97  
% 0.97/0.97  ------ Input Options
% 0.97/0.97  
% 0.97/0.97  --out_options                           all
% 0.97/0.97  --tptp_safe_out                         true
% 0.97/0.97  --problem_path                          ""
% 0.97/0.97  --include_path                          ""
% 0.97/0.97  --clausifier                            res/vclausify_rel
% 0.97/0.97  --clausifier_options                    --mode clausify
% 0.97/0.97  --stdin                                 false
% 0.97/0.97  --stats_out                             all
% 0.97/0.97  
% 0.97/0.97  ------ General Options
% 0.97/0.97  
% 0.97/0.97  --fof                                   false
% 0.97/0.97  --time_out_real                         305.
% 0.97/0.97  --time_out_virtual                      -1.
% 0.97/0.97  --symbol_type_check                     false
% 0.97/0.97  --clausify_out                          false
% 0.97/0.97  --sig_cnt_out                           false
% 0.97/0.97  --trig_cnt_out                          false
% 0.97/0.97  --trig_cnt_out_tolerance                1.
% 0.97/0.97  --trig_cnt_out_sk_spl                   false
% 0.97/0.97  --abstr_cl_out                          false
% 0.97/0.97  
% 0.97/0.97  ------ Global Options
% 0.97/0.97  
% 0.97/0.97  --schedule                              default
% 0.97/0.97  --add_important_lit                     false
% 0.97/0.97  --prop_solver_per_cl                    1000
% 0.97/0.97  --min_unsat_core                        false
% 0.97/0.97  --soft_assumptions                      false
% 0.97/0.97  --soft_lemma_size                       3
% 0.97/0.97  --prop_impl_unit_size                   0
% 0.97/0.97  --prop_impl_unit                        []
% 0.97/0.97  --share_sel_clauses                     true
% 0.97/0.97  --reset_solvers                         false
% 0.97/0.97  --bc_imp_inh                            [conj_cone]
% 0.97/0.97  --conj_cone_tolerance                   3.
% 0.97/0.97  --extra_neg_conj                        none
% 0.97/0.97  --large_theory_mode                     true
% 0.97/0.97  --prolific_symb_bound                   200
% 0.97/0.97  --lt_threshold                          2000
% 0.97/0.97  --clause_weak_htbl                      true
% 0.97/0.97  --gc_record_bc_elim                     false
% 0.97/0.97  
% 0.97/0.97  ------ Preprocessing Options
% 0.97/0.97  
% 0.97/0.97  --preprocessing_flag                    true
% 0.97/0.97  --time_out_prep_mult                    0.1
% 0.97/0.97  --splitting_mode                        input
% 0.97/0.97  --splitting_grd                         true
% 0.97/0.97  --splitting_cvd                         false
% 0.97/0.97  --splitting_cvd_svl                     false
% 0.97/0.97  --splitting_nvd                         32
% 0.97/0.97  --sub_typing                            true
% 0.97/0.97  --prep_gs_sim                           true
% 0.97/0.97  --prep_unflatten                        true
% 0.97/0.97  --prep_res_sim                          true
% 0.97/0.97  --prep_upred                            true
% 0.97/0.97  --prep_sem_filter                       exhaustive
% 0.97/0.97  --prep_sem_filter_out                   false
% 0.97/0.97  --pred_elim                             true
% 0.97/0.97  --res_sim_input                         true
% 0.97/0.97  --eq_ax_congr_red                       true
% 0.97/0.97  --pure_diseq_elim                       true
% 0.97/0.97  --brand_transform                       false
% 0.97/0.97  --non_eq_to_eq                          false
% 0.97/0.97  --prep_def_merge                        true
% 0.97/0.97  --prep_def_merge_prop_impl              false
% 0.97/0.97  --prep_def_merge_mbd                    true
% 0.97/0.97  --prep_def_merge_tr_red                 false
% 0.97/0.97  --prep_def_merge_tr_cl                  false
% 0.97/0.97  --smt_preprocessing                     true
% 0.97/0.97  --smt_ac_axioms                         fast
% 0.97/0.97  --preprocessed_out                      false
% 0.97/0.97  --preprocessed_stats                    false
% 0.97/0.97  
% 0.97/0.97  ------ Abstraction refinement Options
% 0.97/0.97  
% 0.97/0.97  --abstr_ref                             []
% 0.97/0.97  --abstr_ref_prep                        false
% 0.97/0.97  --abstr_ref_until_sat                   false
% 0.97/0.97  --abstr_ref_sig_restrict                funpre
% 0.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.97/0.97  --abstr_ref_under                       []
% 0.97/0.97  
% 0.97/0.97  ------ SAT Options
% 0.97/0.97  
% 0.97/0.97  --sat_mode                              false
% 0.97/0.97  --sat_fm_restart_options                ""
% 0.97/0.97  --sat_gr_def                            false
% 0.97/0.97  --sat_epr_types                         true
% 0.97/0.97  --sat_non_cyclic_types                  false
% 0.97/0.97  --sat_finite_models                     false
% 0.97/0.97  --sat_fm_lemmas                         false
% 0.97/0.97  --sat_fm_prep                           false
% 0.97/0.97  --sat_fm_uc_incr                        true
% 0.97/0.97  --sat_out_model                         small
% 0.97/0.97  --sat_out_clauses                       false
% 0.97/0.97  
% 0.97/0.97  ------ QBF Options
% 0.97/0.97  
% 0.97/0.97  --qbf_mode                              false
% 0.97/0.97  --qbf_elim_univ                         false
% 0.97/0.97  --qbf_dom_inst                          none
% 0.97/0.97  --qbf_dom_pre_inst                      false
% 0.97/0.97  --qbf_sk_in                             false
% 0.97/0.97  --qbf_pred_elim                         true
% 0.97/0.97  --qbf_split                             512
% 0.97/0.97  
% 0.97/0.97  ------ BMC1 Options
% 0.97/0.97  
% 0.97/0.97  --bmc1_incremental                      false
% 0.97/0.97  --bmc1_axioms                           reachable_all
% 0.97/0.97  --bmc1_min_bound                        0
% 0.97/0.97  --bmc1_max_bound                        -1
% 0.97/0.97  --bmc1_max_bound_default                -1
% 0.97/0.97  --bmc1_symbol_reachability              true
% 0.97/0.97  --bmc1_property_lemmas                  false
% 0.97/0.97  --bmc1_k_induction                      false
% 0.97/0.97  --bmc1_non_equiv_states                 false
% 0.97/0.97  --bmc1_deadlock                         false
% 0.97/0.97  --bmc1_ucm                              false
% 0.97/0.97  --bmc1_add_unsat_core                   none
% 0.97/0.97  --bmc1_unsat_core_children              false
% 0.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.97/0.97  --bmc1_out_stat                         full
% 0.97/0.97  --bmc1_ground_init                      false
% 0.97/0.97  --bmc1_pre_inst_next_state              false
% 0.97/0.97  --bmc1_pre_inst_state                   false
% 0.97/0.97  --bmc1_pre_inst_reach_state             false
% 0.97/0.97  --bmc1_out_unsat_core                   false
% 0.97/0.97  --bmc1_aig_witness_out                  false
% 0.97/0.97  --bmc1_verbose                          false
% 0.97/0.97  --bmc1_dump_clauses_tptp                false
% 0.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.97/0.97  --bmc1_dump_file                        -
% 0.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.97/0.97  --bmc1_ucm_extend_mode                  1
% 0.97/0.97  --bmc1_ucm_init_mode                    2
% 0.97/0.97  --bmc1_ucm_cone_mode                    none
% 0.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.97/0.97  --bmc1_ucm_relax_model                  4
% 0.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.97/0.97  --bmc1_ucm_layered_model                none
% 0.97/0.97  --bmc1_ucm_max_lemma_size               10
% 0.97/0.97  
% 0.97/0.97  ------ AIG Options
% 0.97/0.97  
% 0.97/0.97  --aig_mode                              false
% 0.97/0.97  
% 0.97/0.97  ------ Instantiation Options
% 0.97/0.97  
% 0.97/0.97  --instantiation_flag                    true
% 0.97/0.97  --inst_sos_flag                         false
% 0.97/0.97  --inst_sos_phase                        true
% 0.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.97/0.97  --inst_lit_sel_side                     none
% 0.97/0.97  --inst_solver_per_active                1400
% 0.97/0.97  --inst_solver_calls_frac                1.
% 0.97/0.97  --inst_passive_queue_type               priority_queues
% 0.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.97/0.97  --inst_passive_queues_freq              [25;2]
% 0.97/0.97  --inst_dismatching                      true
% 0.97/0.97  --inst_eager_unprocessed_to_passive     true
% 0.97/0.97  --inst_prop_sim_given                   true
% 0.97/0.97  --inst_prop_sim_new                     false
% 0.97/0.97  --inst_subs_new                         false
% 0.97/0.97  --inst_eq_res_simp                      false
% 0.97/0.97  --inst_subs_given                       false
% 0.97/0.97  --inst_orphan_elimination               true
% 0.97/0.97  --inst_learning_loop_flag               true
% 0.97/0.97  --inst_learning_start                   3000
% 0.97/0.97  --inst_learning_factor                  2
% 0.97/0.97  --inst_start_prop_sim_after_learn       3
% 0.97/0.97  --inst_sel_renew                        solver
% 0.97/0.97  --inst_lit_activity_flag                true
% 0.97/0.97  --inst_restr_to_given                   false
% 0.97/0.97  --inst_activity_threshold               500
% 0.97/0.97  --inst_out_proof                        true
% 0.97/0.97  
% 0.97/0.97  ------ Resolution Options
% 0.97/0.97  
% 0.97/0.97  --resolution_flag                       false
% 0.97/0.97  --res_lit_sel                           adaptive
% 0.97/0.97  --res_lit_sel_side                      none
% 0.97/0.97  --res_ordering                          kbo
% 0.97/0.97  --res_to_prop_solver                    active
% 0.97/0.97  --res_prop_simpl_new                    false
% 0.97/0.97  --res_prop_simpl_given                  true
% 0.97/0.97  --res_passive_queue_type                priority_queues
% 0.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.97/0.97  --res_passive_queues_freq               [15;5]
% 0.97/0.97  --res_forward_subs                      full
% 0.97/0.97  --res_backward_subs                     full
% 0.97/0.97  --res_forward_subs_resolution           true
% 0.97/0.97  --res_backward_subs_resolution          true
% 0.97/0.97  --res_orphan_elimination                true
% 0.97/0.97  --res_time_limit                        2.
% 0.97/0.97  --res_out_proof                         true
% 0.97/0.97  
% 0.97/0.97  ------ Superposition Options
% 0.97/0.97  
% 0.97/0.97  --superposition_flag                    false
% 0.97/0.97  --sup_passive_queue_type                priority_queues
% 0.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.97/0.97  --demod_completeness_check              fast
% 0.97/0.97  --demod_use_ground                      true
% 0.97/0.97  --sup_to_prop_solver                    passive
% 0.97/0.97  --sup_prop_simpl_new                    true
% 0.97/0.97  --sup_prop_simpl_given                  true
% 0.97/0.97  --sup_fun_splitting                     false
% 0.97/0.97  --sup_smt_interval                      50000
% 0.97/0.97  
% 0.97/0.97  ------ Superposition Simplification Setup
% 0.97/0.97  
% 0.97/0.97  --sup_indices_passive                   []
% 0.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.97  --sup_full_bw                           [BwDemod]
% 0.97/0.97  --sup_immed_triv                        [TrivRules]
% 0.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.97  --sup_immed_bw_main                     []
% 0.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.97  
% 0.97/0.97  ------ Combination Options
% 0.97/0.97  
% 0.97/0.97  --comb_res_mult                         3
% 0.97/0.97  --comb_sup_mult                         2
% 0.97/0.97  --comb_inst_mult                        10
% 0.97/0.97  
% 0.97/0.97  ------ Debug Options
% 0.97/0.97  
% 0.97/0.97  --dbg_backtrace                         false
% 0.97/0.97  --dbg_dump_prop_clauses                 false
% 0.97/0.97  --dbg_dump_prop_clauses_file            -
% 0.97/0.97  --dbg_out_stat                          false
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  ------ Proving...
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  % SZS status Theorem for theBenchmark.p
% 0.97/0.97  
% 0.97/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.97/0.97  
% 0.97/0.97  fof(f6,axiom,(
% 0.97/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f17,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/0.97    inference(ennf_transformation,[],[f6])).
% 0.97/0.97  
% 0.97/0.97  fof(f18,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(flattening,[],[f17])).
% 0.97/0.97  
% 0.97/0.97  fof(f27,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(nnf_transformation,[],[f18])).
% 0.97/0.97  
% 0.97/0.97  fof(f28,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(rectify,[],[f27])).
% 0.97/0.97  
% 0.97/0.97  fof(f29,plain,(
% 0.97/0.97    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f30,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 0.97/0.97  
% 0.97/0.97  fof(f44,plain,(
% 0.97/0.97    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f30])).
% 0.97/0.97  
% 0.97/0.97  fof(f8,conjecture,(
% 0.97/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f9,negated_conjecture,(
% 0.97/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.97/0.97    inference(negated_conjecture,[],[f8])).
% 0.97/0.97  
% 0.97/0.97  fof(f21,plain,(
% 0.97/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & (v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5))) & m1_subset_1(X5,u1_struct_0(X2))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.97/0.97    inference(ennf_transformation,[],[f9])).
% 0.97/0.97  
% 0.97/0.97  fof(f22,plain,(
% 0.97/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.97/0.97    inference(flattening,[],[f21])).
% 0.97/0.97  
% 0.97/0.97  fof(f36,plain,(
% 0.97/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),sK7) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,sK7) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f35,plain,(
% 0.97/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,sK6),X5) & v5_pre_topc(sK6,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f34,plain,(
% 0.97/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),sK5,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,sK5,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f33,plain,(
% 0.97/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(sK4,X1,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(sK4,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f32,plain,(
% 0.97/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,X0,sK3) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f31,plain,(
% 0.97/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,sK2,X1) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f37,plain,(
% 0.97/0.97    (((((~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,sK7) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f36,f35,f34,f33,f32,f31])).
% 0.97/0.97  
% 0.97/0.97  fof(f65,plain,(
% 0.97/0.97    v5_pre_topc(sK6,sK2,sK3)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f48,plain,(
% 0.97/0.97    ~v2_struct_0(sK2)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f49,plain,(
% 0.97/0.97    v2_pre_topc(sK2)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f50,plain,(
% 0.97/0.97    l1_pre_topc(sK2)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f51,plain,(
% 0.97/0.97    ~v2_struct_0(sK3)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f52,plain,(
% 0.97/0.97    v2_pre_topc(sK3)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f53,plain,(
% 0.97/0.97    l1_pre_topc(sK3)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f60,plain,(
% 0.97/0.97    v1_funct_1(sK6)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f61,plain,(
% 0.97/0.97    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f62,plain,(
% 0.97/0.97    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f2,axiom,(
% 0.97/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f10,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.97/0.97    inference(ennf_transformation,[],[f2])).
% 0.97/0.97  
% 0.97/0.97  fof(f40,plain,(
% 0.97/0.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f10])).
% 0.97/0.97  
% 0.97/0.97  fof(f7,axiom,(
% 0.97/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f19,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/0.97    inference(ennf_transformation,[],[f7])).
% 0.97/0.97  
% 0.97/0.97  fof(f20,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(flattening,[],[f19])).
% 0.97/0.97  
% 0.97/0.97  fof(f47,plain,(
% 0.97/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f20])).
% 0.97/0.97  
% 0.97/0.97  fof(f67,plain,(
% 0.97/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.97    inference(equality_resolution,[],[f47])).
% 0.97/0.97  
% 0.97/0.97  fof(f3,axiom,(
% 0.97/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f11,plain,(
% 0.97/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.97/0.97    inference(ennf_transformation,[],[f3])).
% 0.97/0.97  
% 0.97/0.97  fof(f12,plain,(
% 0.97/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.97/0.97    inference(flattening,[],[f11])).
% 0.97/0.97  
% 0.97/0.97  fof(f41,plain,(
% 0.97/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f12])).
% 0.97/0.97  
% 0.97/0.97  fof(f4,axiom,(
% 0.97/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f13,plain,(
% 0.97/0.97    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/0.97    inference(ennf_transformation,[],[f4])).
% 0.97/0.97  
% 0.97/0.97  fof(f14,plain,(
% 0.97/0.97    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(flattening,[],[f13])).
% 0.97/0.97  
% 0.97/0.97  fof(f42,plain,(
% 0.97/0.97    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f14])).
% 0.97/0.97  
% 0.97/0.97  fof(f1,axiom,(
% 0.97/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f23,plain,(
% 0.97/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.97/0.97    inference(nnf_transformation,[],[f1])).
% 0.97/0.97  
% 0.97/0.97  fof(f24,plain,(
% 0.97/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.97/0.97    inference(rectify,[],[f23])).
% 0.97/0.97  
% 0.97/0.97  fof(f25,plain,(
% 0.97/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.97/0.97    introduced(choice_axiom,[])).
% 0.97/0.97  
% 0.97/0.97  fof(f26,plain,(
% 0.97/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 0.97/0.97  
% 0.97/0.97  fof(f38,plain,(
% 0.97/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f26])).
% 0.97/0.97  
% 0.97/0.97  fof(f5,axiom,(
% 0.97/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.97  
% 0.97/0.97  fof(f15,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/0.97    inference(ennf_transformation,[],[f5])).
% 0.97/0.97  
% 0.97/0.97  fof(f16,plain,(
% 0.97/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.97    inference(flattening,[],[f15])).
% 0.97/0.97  
% 0.97/0.97  fof(f43,plain,(
% 0.97/0.97    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.97    inference(cnf_transformation,[],[f16])).
% 0.97/0.97  
% 0.97/0.97  fof(f66,plain,(
% 0.97/0.97    ~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f64,plain,(
% 0.97/0.97    r1_tmap_1(sK4,sK2,sK5,sK7)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f63,plain,(
% 0.97/0.97    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f59,plain,(
% 0.97/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f58,plain,(
% 0.97/0.97    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f57,plain,(
% 0.97/0.97    v1_funct_1(sK5)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f56,plain,(
% 0.97/0.97    l1_pre_topc(sK4)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f55,plain,(
% 0.97/0.97    v2_pre_topc(sK4)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  fof(f54,plain,(
% 0.97/0.97    ~v2_struct_0(sK4)),
% 0.97/0.97    inference(cnf_transformation,[],[f37])).
% 0.97/0.97  
% 0.97/0.97  cnf(c_8,plain,
% 0.97/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 0.97/0.97      | ~ v5_pre_topc(X2,X0,X1)
% 0.97/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 0.97/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.97/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.97/0.97      | v2_struct_0(X1)
% 0.97/0.97      | v2_struct_0(X0)
% 0.97/0.97      | ~ v2_pre_topc(X1)
% 0.97/0.97      | ~ v2_pre_topc(X0)
% 0.97/0.97      | ~ l1_pre_topc(X1)
% 0.97/0.97      | ~ l1_pre_topc(X0)
% 0.97/0.97      | ~ v1_funct_1(X2) ),
% 0.97/0.97      inference(cnf_transformation,[],[f44]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_11,negated_conjecture,
% 0.97/0.97      ( v5_pre_topc(sK6,sK2,sK3) ),
% 0.97/0.97      inference(cnf_transformation,[],[f65]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_390,plain,
% 0.97/0.97      ( r1_tmap_1(sK2,sK3,sK6,X0)
% 0.97/0.97      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.97/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.97/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.97/0.97      | v2_struct_0(sK2)
% 0.97/0.97      | v2_struct_0(sK3)
% 0.97/0.97      | ~ v2_pre_topc(sK2)
% 0.97/0.97      | ~ v2_pre_topc(sK3)
% 0.97/0.97      | ~ l1_pre_topc(sK2)
% 0.97/0.97      | ~ l1_pre_topc(sK3)
% 0.97/0.97      | ~ v1_funct_1(sK6) ),
% 0.97/0.97      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_28,negated_conjecture,
% 0.97/0.97      ( ~ v2_struct_0(sK2) ),
% 0.97/0.97      inference(cnf_transformation,[],[f48]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_27,negated_conjecture,
% 0.97/0.97      ( v2_pre_topc(sK2) ),
% 0.97/0.97      inference(cnf_transformation,[],[f49]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_26,negated_conjecture,
% 0.97/0.97      ( l1_pre_topc(sK2) ),
% 0.97/0.97      inference(cnf_transformation,[],[f50]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_25,negated_conjecture,
% 0.97/0.97      ( ~ v2_struct_0(sK3) ),
% 0.97/0.97      inference(cnf_transformation,[],[f51]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_24,negated_conjecture,
% 0.97/0.97      ( v2_pre_topc(sK3) ),
% 0.97/0.97      inference(cnf_transformation,[],[f52]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_23,negated_conjecture,
% 0.97/0.97      ( l1_pre_topc(sK3) ),
% 0.97/0.97      inference(cnf_transformation,[],[f53]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_16,negated_conjecture,
% 0.97/0.97      ( v1_funct_1(sK6) ),
% 0.97/0.97      inference(cnf_transformation,[],[f60]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_15,negated_conjecture,
% 0.97/0.97      ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 0.97/0.97      inference(cnf_transformation,[],[f61]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_14,negated_conjecture,
% 0.97/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 0.97/0.97      inference(cnf_transformation,[],[f62]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_394,plain,
% 0.97/0.97      ( r1_tmap_1(sK2,sK3,sK6,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 0.97/0.97      inference(global_propositional_subsumption,
% 0.97/0.97                [status(thm)],
% 0.97/0.97                [c_390,c_28,c_27,c_26,c_25,c_24,c_23,c_16,c_15,c_14]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_569,plain,
% 0.97/0.97      ( r1_tmap_1(sK2,sK3,sK6,X0_53)
% 0.97/0.97      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 0.97/0.97      inference(subtyping,[status(esa)],[c_394]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_787,plain,
% 0.97/0.97      ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
% 0.97/0.97      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_569]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_2,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.97/0.97      | ~ v1_xboole_0(X1)
% 0.97/0.97      | v1_xboole_0(X0) ),
% 0.97/0.97      inference(cnf_transformation,[],[f40]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_594,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 0.97/0.97      | ~ v1_xboole_0(X1_53)
% 0.97/0.97      | v1_xboole_0(X0_53) ),
% 0.97/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_769,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 0.97/0.97      | v1_xboole_0(X0_53)
% 0.97/0.97      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_594]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_784,plain,
% 0.97/0.97      ( ~ m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
% 0.97/0.97      | v1_xboole_0(k1_connsp_2(sK4,sK7))
% 0.97/0.97      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_769]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_9,plain,
% 0.97/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 0.97/0.97      | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 0.97/0.97      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
% 0.97/0.97      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 0.97/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 0.97/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.97/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 0.97/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.97/0.97      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
% 0.97/0.97      | v2_struct_0(X4)
% 0.97/0.97      | v2_struct_0(X1)
% 0.97/0.97      | v2_struct_0(X0)
% 0.97/0.97      | ~ v2_pre_topc(X4)
% 0.97/0.97      | ~ v2_pre_topc(X1)
% 0.97/0.97      | ~ v2_pre_topc(X0)
% 0.97/0.97      | ~ l1_pre_topc(X4)
% 0.97/0.97      | ~ l1_pre_topc(X1)
% 0.97/0.97      | ~ l1_pre_topc(X0)
% 0.97/0.97      | ~ v1_funct_1(X5)
% 0.97/0.97      | ~ v1_funct_1(X2) ),
% 0.97/0.97      inference(cnf_transformation,[],[f67]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_591,plain,
% 0.97/0.97      ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
% 0.97/0.97      | ~ r1_tmap_1(X1_52,X2_52,X2_53,k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,X1_53))
% 0.97/0.97      | r1_tmap_1(X0_52,X2_52,k1_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),u1_struct_0(X1_52),u1_struct_0(X2_52),X0_53,X2_53),X1_53)
% 0.97/0.97      | ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 0.97/0.97      | ~ v1_funct_2(X2_53,u1_struct_0(X1_52),u1_struct_0(X2_52))
% 0.97/0.97      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 0.97/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 0.97/0.97      | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X2_52))))
% 0.97/0.97      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,X1_53),u1_struct_0(X1_52))
% 0.97/0.97      | v2_struct_0(X0_52)
% 0.97/0.97      | v2_struct_0(X1_52)
% 0.97/0.97      | v2_struct_0(X2_52)
% 0.97/0.97      | ~ v2_pre_topc(X0_52)
% 0.97/0.97      | ~ v2_pre_topc(X1_52)
% 0.97/0.97      | ~ v2_pre_topc(X2_52)
% 0.97/0.97      | ~ l1_pre_topc(X0_52)
% 0.97/0.97      | ~ l1_pre_topc(X1_52)
% 0.97/0.97      | ~ l1_pre_topc(X2_52)
% 0.97/0.97      | ~ v1_funct_1(X2_53)
% 0.97/0.97      | ~ v1_funct_1(X0_53) ),
% 0.97/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_740,plain,
% 0.97/0.97      ( ~ r1_tmap_1(X0_52,X1_52,X0_53,k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_52),X1_53,sK7))
% 0.97/0.97      | ~ r1_tmap_1(sK4,X0_52,X1_53,sK7)
% 0.97/0.97      | r1_tmap_1(sK4,X1_52,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X0_52),u1_struct_0(X0_52),u1_struct_0(X1_52),X1_53,X0_53),sK7)
% 0.97/0.97      | ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 0.97/0.97      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_52))
% 0.97/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 0.97/0.97      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 0.97/0.97      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(X0_52),X1_53,sK7),u1_struct_0(X0_52))
% 0.97/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | v2_struct_0(X0_52)
% 0.97/0.97      | v2_struct_0(X1_52)
% 0.97/0.97      | v2_struct_0(sK4)
% 0.97/0.97      | ~ v2_pre_topc(X0_52)
% 0.97/0.97      | ~ v2_pre_topc(X1_52)
% 0.97/0.97      | ~ v2_pre_topc(sK4)
% 0.97/0.97      | ~ l1_pre_topc(X0_52)
% 0.97/0.97      | ~ l1_pre_topc(X1_52)
% 0.97/0.97      | ~ l1_pre_topc(sK4)
% 0.97/0.97      | ~ v1_funct_1(X1_53)
% 0.97/0.97      | ~ v1_funct_1(X0_53) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_591]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_759,plain,
% 0.97/0.97      ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),X0_53,sK7))
% 0.97/0.97      | ~ r1_tmap_1(sK4,sK2,X0_53,sK7)
% 0.97/0.97      | r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X0_53,sK6),sK7)
% 0.97/0.97      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK2))
% 0.97/0.97      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.97/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 0.97/0.97      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),X0_53,sK7),u1_struct_0(sK2))
% 0.97/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.97/0.97      | v2_struct_0(sK2)
% 0.97/0.97      | v2_struct_0(sK3)
% 0.97/0.97      | v2_struct_0(sK4)
% 0.97/0.97      | ~ v2_pre_topc(sK2)
% 0.97/0.97      | ~ v2_pre_topc(sK3)
% 0.97/0.97      | ~ v2_pre_topc(sK4)
% 0.97/0.97      | ~ l1_pre_topc(sK2)
% 0.97/0.97      | ~ l1_pre_topc(sK3)
% 0.97/0.97      | ~ l1_pre_topc(sK4)
% 0.97/0.97      | ~ v1_funct_1(X0_53)
% 0.97/0.97      | ~ v1_funct_1(sK6) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_740]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_761,plain,
% 0.97/0.97      ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
% 0.97/0.97      | ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 0.97/0.97      | r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
% 0.97/0.97      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.97/0.97      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 0.97/0.97      | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
% 0.97/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.97/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 0.97/0.97      | v2_struct_0(sK2)
% 0.97/0.97      | v2_struct_0(sK3)
% 0.97/0.97      | v2_struct_0(sK4)
% 0.97/0.97      | ~ v2_pre_topc(sK2)
% 0.97/0.97      | ~ v2_pre_topc(sK3)
% 0.97/0.97      | ~ v2_pre_topc(sK4)
% 0.97/0.97      | ~ l1_pre_topc(sK2)
% 0.97/0.97      | ~ l1_pre_topc(sK3)
% 0.97/0.97      | ~ l1_pre_topc(sK4)
% 0.97/0.97      | ~ v1_funct_1(sK6)
% 0.97/0.97      | ~ v1_funct_1(sK5) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_759]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_3,plain,
% 0.97/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 0.97/0.97      | ~ m1_subset_1(X3,X1)
% 0.97/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.97/0.97      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 0.97/0.97      | ~ v1_funct_1(X0)
% 0.97/0.97      | v1_xboole_0(X1) ),
% 0.97/0.97      inference(cnf_transformation,[],[f41]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_593,plain,
% 0.97/0.97      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 0.97/0.97      | ~ m1_subset_1(X3_53,X1_53)
% 0.97/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 0.97/0.97      | m1_subset_1(k3_funct_2(X1_53,X2_53,X0_53,X3_53),X2_53)
% 0.97/0.97      | ~ v1_funct_1(X0_53)
% 0.97/0.97      | v1_xboole_0(X1_53) ),
% 0.97/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_719,plain,
% 0.97/0.97      ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),X1_53)
% 0.97/0.97      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_53)))
% 0.97/0.97      | m1_subset_1(k3_funct_2(u1_struct_0(sK4),X1_53,X0_53,sK7),X1_53)
% 0.97/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | ~ v1_funct_1(X0_53)
% 0.97/0.97      | v1_xboole_0(u1_struct_0(sK4)) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_593]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_750,plain,
% 0.97/0.97      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 0.97/0.97      | m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
% 0.97/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 0.97/0.97      | ~ v1_funct_1(sK5)
% 0.97/0.97      | v1_xboole_0(u1_struct_0(sK4)) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_719]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_4,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.97/0.97      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.97      | v2_struct_0(X1)
% 0.97/0.97      | ~ v2_pre_topc(X1)
% 0.97/0.97      | ~ l1_pre_topc(X1) ),
% 0.97/0.97      inference(cnf_transformation,[],[f42]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_592,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 0.97/0.97      | m1_subset_1(k1_connsp_2(X0_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
% 0.97/0.97      | v2_struct_0(X0_52)
% 0.97/0.97      | ~ v2_pre_topc(X0_52)
% 0.97/0.97      | ~ l1_pre_topc(X0_52) ),
% 0.97/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_716,plain,
% 0.97/0.97      ( m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
% 0.97/0.97      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | v2_struct_0(sK4)
% 0.97/0.97      | ~ v2_pre_topc(sK4)
% 0.97/0.97      | ~ l1_pre_topc(sK4) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_592]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_1,plain,
% 0.97/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 0.97/0.97      inference(cnf_transformation,[],[f38]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_5,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.97/0.97      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 0.97/0.97      | v2_struct_0(X1)
% 0.97/0.97      | ~ v2_pre_topc(X1)
% 0.97/0.97      | ~ l1_pre_topc(X1) ),
% 0.97/0.97      inference(cnf_transformation,[],[f43]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_282,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.97/0.97      | v2_struct_0(X1)
% 0.97/0.97      | ~ v2_pre_topc(X1)
% 0.97/0.97      | ~ l1_pre_topc(X1)
% 0.97/0.97      | ~ v1_xboole_0(k1_connsp_2(X1,X0)) ),
% 0.97/0.97      inference(resolution,[status(thm)],[c_1,c_5]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_572,plain,
% 0.97/0.97      ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 0.97/0.97      | v2_struct_0(X0_52)
% 0.97/0.97      | ~ v2_pre_topc(X0_52)
% 0.97/0.97      | ~ l1_pre_topc(X0_52)
% 0.97/0.97      | ~ v1_xboole_0(k1_connsp_2(X0_52,X0_53)) ),
% 0.97/0.97      inference(subtyping,[status(esa)],[c_282]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_713,plain,
% 0.97/0.97      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 0.97/0.97      | v2_struct_0(sK4)
% 0.97/0.97      | ~ v2_pre_topc(sK4)
% 0.97/0.97      | ~ l1_pre_topc(sK4)
% 0.97/0.97      | ~ v1_xboole_0(k1_connsp_2(sK4,sK7)) ),
% 0.97/0.97      inference(instantiation,[status(thm)],[c_572]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_10,negated_conjecture,
% 0.97/0.97      ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
% 0.97/0.97      inference(cnf_transformation,[],[f66]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_12,negated_conjecture,
% 0.97/0.97      ( r1_tmap_1(sK4,sK2,sK5,sK7) ),
% 0.97/0.97      inference(cnf_transformation,[],[f64]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_13,negated_conjecture,
% 0.97/0.97      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 0.97/0.97      inference(cnf_transformation,[],[f63]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_17,negated_conjecture,
% 0.97/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 0.97/0.97      inference(cnf_transformation,[],[f59]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_18,negated_conjecture,
% 0.97/0.97      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 0.97/0.97      inference(cnf_transformation,[],[f58]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_19,negated_conjecture,
% 0.97/0.97      ( v1_funct_1(sK5) ),
% 0.97/0.97      inference(cnf_transformation,[],[f57]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_20,negated_conjecture,
% 0.97/0.97      ( l1_pre_topc(sK4) ),
% 0.97/0.97      inference(cnf_transformation,[],[f56]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_21,negated_conjecture,
% 0.97/0.97      ( v2_pre_topc(sK4) ),
% 0.97/0.97      inference(cnf_transformation,[],[f55]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(c_22,negated_conjecture,
% 0.97/0.97      ( ~ v2_struct_0(sK4) ),
% 0.97/0.97      inference(cnf_transformation,[],[f54]) ).
% 0.97/0.97  
% 0.97/0.97  cnf(contradiction,plain,
% 0.97/0.97      ( $false ),
% 0.97/0.97      inference(minisat,
% 0.97/0.97                [status(thm)],
% 0.97/0.97                [c_787,c_784,c_761,c_750,c_716,c_713,c_10,c_12,c_13,c_14,
% 0.97/0.97                 c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,
% 0.97/0.97                 c_26,c_27,c_28]) ).
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 0.97/0.97  
% 0.97/0.97  ------                               Statistics
% 0.97/0.97  
% 0.97/0.97  ------ General
% 0.97/0.97  
% 0.97/0.97  abstr_ref_over_cycles:                  0
% 0.97/0.97  abstr_ref_under_cycles:                 0
% 0.97/0.97  gc_basic_clause_elim:                   0
% 0.97/0.97  forced_gc_time:                         0
% 0.97/0.97  parsing_time:                           0.01
% 0.97/0.97  unif_index_cands_time:                  0.
% 0.97/0.97  unif_index_add_time:                    0.
% 0.97/0.97  orderings_time:                         0.
% 0.97/0.97  out_proof_time:                         0.012
% 0.97/0.97  total_time:                             0.068
% 0.97/0.97  num_of_symbols:                         57
% 0.97/0.97  num_of_terms:                           1202
% 0.97/0.97  
% 0.97/0.97  ------ Preprocessing
% 0.97/0.97  
% 0.97/0.97  num_of_splits:                          0
% 0.97/0.97  num_of_split_atoms:                     0
% 0.97/0.97  num_of_reused_defs:                     0
% 0.97/0.97  num_eq_ax_congr_red:                    0
% 0.97/0.97  num_of_sem_filtered_clauses:            0
% 0.97/0.97  num_of_subtypes:                        2
% 0.97/0.97  monotx_restored_types:                  0
% 0.97/0.97  sat_num_of_epr_types:                   0
% 0.97/0.97  sat_num_of_non_cyclic_types:            0
% 0.97/0.97  sat_guarded_non_collapsed_types:        0
% 0.97/0.97  num_pure_diseq_elim:                    0
% 0.97/0.97  simp_replaced_by:                       0
% 0.97/0.97  res_preprocessed:                       55
% 0.97/0.97  prep_upred:                             0
% 0.97/0.97  prep_unflattend:                        0
% 0.97/0.97  smt_new_axioms:                         0
% 0.97/0.97  pred_elim_cands:                        8
% 0.97/0.97  pred_elim:                              2
% 0.97/0.97  pred_elim_cl:                           3
% 0.97/0.97  pred_elim_cycles:                       4
% 0.97/0.97  merged_defs:                            0
% 0.97/0.97  merged_defs_ncl:                        0
% 0.97/0.97  bin_hyper_res:                          0
% 0.97/0.97  prep_cycles:                            2
% 0.97/0.97  pred_elim_time:                         0.004
% 0.97/0.97  splitting_time:                         0.
% 0.97/0.97  sem_filter_time:                        0.
% 0.97/0.97  monotx_time:                            0.
% 0.97/0.97  subtype_inf_time:                       0.
% 0.97/0.97  
% 0.97/0.97  ------ Problem properties
% 0.97/0.97  
% 0.97/0.97  clauses:                                26
% 0.97/0.97  conjectures:                            18
% 0.97/0.97  epr:                                    12
% 0.97/0.97  horn:                                   21
% 0.97/0.97  ground:                                 18
% 0.97/0.97  unary:                                  18
% 0.97/0.97  binary:                                 1
% 0.97/0.97  lits:                                   83
% 0.97/0.97  lits_eq:                                0
% 0.97/0.97  fd_pure:                                0
% 0.97/0.97  fd_pseudo:                              0
% 0.97/0.97  fd_cond:                                0
% 0.97/0.97  fd_pseudo_cond:                         0
% 0.97/0.97  ac_symbols:                             0
% 0.97/0.97  
% 0.97/0.97  ------ Propositional Solver
% 0.97/0.97  
% 0.97/0.97  prop_solver_calls:                      16
% 0.97/0.97  prop_fast_solver_calls:                 400
% 0.97/0.97  smt_solver_calls:                       0
% 0.97/0.97  smt_fast_solver_calls:                  0
% 0.97/0.97  prop_num_of_clauses:                    182
% 0.97/0.97  prop_preprocess_simplified:             1310
% 0.97/0.97  prop_fo_subsumed:                       9
% 0.97/0.97  prop_solver_time:                       0.
% 0.97/0.97  smt_solver_time:                        0.
% 0.97/0.97  smt_fast_solver_time:                   0.
% 0.97/0.97  prop_fast_solver_time:                  0.
% 0.97/0.97  prop_unsat_core_time:                   0.
% 0.97/0.97  
% 0.97/0.97  ------ QBF
% 0.97/0.97  
% 0.97/0.97  qbf_q_res:                              0
% 0.97/0.97  qbf_num_tautologies:                    0
% 0.97/0.97  qbf_prep_cycles:                        0
% 0.97/0.97  
% 0.97/0.97  ------ BMC1
% 0.97/0.97  
% 0.97/0.97  bmc1_current_bound:                     -1
% 0.97/0.97  bmc1_last_solved_bound:                 -1
% 0.97/0.97  bmc1_unsat_core_size:                   -1
% 0.97/0.97  bmc1_unsat_core_parents_size:           -1
% 0.97/0.97  bmc1_merge_next_fun:                    0
% 0.97/0.97  bmc1_unsat_core_clauses_time:           0.
% 0.97/0.97  
% 0.97/0.97  ------ Instantiation
% 0.97/0.97  
% 0.97/0.97  inst_num_of_clauses:                    44
% 0.97/0.97  inst_num_in_passive:                    0
% 0.97/0.97  inst_num_in_active:                     43
% 0.97/0.97  inst_num_in_unprocessed:                0
% 0.97/0.97  inst_num_of_loops:                      49
% 0.97/0.97  inst_num_of_learning_restarts:          0
% 0.97/0.97  inst_num_moves_active_passive:          1
% 0.97/0.97  inst_lit_activity:                      0
% 0.97/0.97  inst_lit_activity_moves:                0
% 0.97/0.97  inst_num_tautologies:                   0
% 0.97/0.97  inst_num_prop_implied:                  0
% 0.97/0.97  inst_num_existing_simplified:           0
% 0.97/0.97  inst_num_eq_res_simplified:             0
% 0.97/0.97  inst_num_child_elim:                    0
% 0.97/0.97  inst_num_of_dismatching_blockings:      0
% 0.97/0.97  inst_num_of_non_proper_insts:           18
% 0.97/0.97  inst_num_of_duplicates:                 0
% 0.97/0.97  inst_inst_num_from_inst_to_res:         0
% 0.97/0.97  inst_dismatching_checking_time:         0.
% 0.97/0.97  
% 0.97/0.97  ------ Resolution
% 0.97/0.97  
% 0.97/0.97  res_num_of_clauses:                     0
% 0.97/0.97  res_num_in_passive:                     0
% 0.97/0.97  res_num_in_active:                      0
% 0.97/0.97  res_num_of_loops:                       57
% 0.97/0.97  res_forward_subset_subsumed:            0
% 0.97/0.97  res_backward_subset_subsumed:           0
% 0.97/0.97  res_forward_subsumed:                   0
% 0.97/0.97  res_backward_subsumed:                  0
% 0.97/0.97  res_forward_subsumption_resolution:     0
% 0.97/0.97  res_backward_subsumption_resolution:    0
% 0.97/0.97  res_clause_to_clause_subsumption:       0
% 0.97/0.97  res_orphan_elimination:                 0
% 0.97/0.97  res_tautology_del:                      1
% 0.97/0.97  res_num_eq_res_simplified:              0
% 0.97/0.97  res_num_sel_changes:                    0
% 0.97/0.97  res_moves_from_active_to_pass:          0
% 0.97/0.97  
% 0.97/0.97  ------ Superposition
% 0.97/0.97  
% 0.97/0.97  sup_time_total:                         0.
% 0.97/0.97  sup_time_generating:                    0.
% 0.97/0.97  sup_time_sim_full:                      0.
% 0.97/0.97  sup_time_sim_immed:                     0.
% 0.97/0.97  
% 0.97/0.97  sup_num_of_clauses:                     0
% 0.97/0.97  sup_num_in_active:                      0
% 0.97/0.97  sup_num_in_passive:                     0
% 0.97/0.97  sup_num_of_loops:                       0
% 0.97/0.97  sup_fw_superposition:                   0
% 0.97/0.97  sup_bw_superposition:                   0
% 0.97/0.97  sup_immediate_simplified:               0
% 0.97/0.97  sup_given_eliminated:                   0
% 0.97/0.97  comparisons_done:                       0
% 0.97/0.97  comparisons_avoided:                    0
% 0.97/0.97  
% 0.97/0.97  ------ Simplifications
% 0.97/0.97  
% 0.97/0.97  
% 0.97/0.97  sim_fw_subset_subsumed:                 0
% 0.97/0.97  sim_bw_subset_subsumed:                 0
% 0.97/0.97  sim_fw_subsumed:                        0
% 0.97/0.97  sim_bw_subsumed:                        0
% 0.97/0.97  sim_fw_subsumption_res:                 0
% 0.97/0.97  sim_bw_subsumption_res:                 0
% 0.97/0.97  sim_tautology_del:                      0
% 0.97/0.97  sim_eq_tautology_del:                   0
% 0.97/0.97  sim_eq_res_simp:                        0
% 0.97/0.97  sim_fw_demodulated:                     0
% 0.97/0.97  sim_bw_demodulated:                     0
% 0.97/0.97  sim_light_normalised:                   0
% 0.97/0.97  sim_joinable_taut:                      0
% 0.97/0.97  sim_joinable_simp:                      0
% 0.97/0.97  sim_ac_normalised:                      0
% 0.97/0.97  sim_smt_subsumption:                    0
% 0.97/0.97  
%------------------------------------------------------------------------------
